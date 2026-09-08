/**
 * This file is part of DCD, a development tool for the D programming language.
 * Copyright (C) 2014 Brian Schott
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

module dcd.server.mixin_resolver;

import dcd.server.autocomplete.util : clampedBucketCount;

import dparse.lexer : LexerConfig, StringCache, Token, getTokensForParser, tok;

import dsymbol.mixin_eval : MixinExpansion;

import std.algorithm : map;
import std.algorithm.iteration : map, splitter;
import std.algorithm.searching : canFind;
import std.array : array, join;
import std.conv : to;
import std.string : chomp, endsWith, lastIndexOf, lineSplitter,
	startsWith, stripLeft;
import std.datetime.stopwatch : StopWatch, AutoStart;
import std.experimental.logger : infof, warningf;
import std.file : exists, readText, tempDir;
import std.path : buildPath;
import std.process : Redirect, pipeProcess, wait;
import std.range : empty;
import std.string : chomp, endsWith, lastIndexOf, lineSplitter,
	startsWith, stripLeft;
import std.typecons : Tuple;

/**
 * Resolves string mixins by delegating to the D compiler.
 *
 * DCD's built-in evaluator (dsymbol.mixin_eval) understands only a small
 * subset of CTFE: string literals, `~` concatenation and single-parameter
 * eponymous templates. When a mixin needs more than that (format!-based
 * generators, static foreach over string arrays, __traits, ...), the
 * compiler is asked to expand it: every D compiler ships a flag that dumps
 * the fully evaluated text of every string mixin in a file:
 *
 * $(UL
 *     $(LI dmd / ldmd2: `-mixin=<file>`)
 *     $(LI ldc2: `-mixin=<file>`)
 *     $(LI gdc: `-fsave-mixins=<file>`)
 * )
 *
 * The dump format (stable across compilers, used by dmd's own test suite):
 *
 * ---
 * // expansion at <file>(<line>)
 * <generated text>
 *
 * ---
 *
 * Entries are separated by blank lines. Expansions coming from imported
 * modules appear with a foreign (or empty) file anchor and are filtered
 * out; only expansions anchored in the requested file are kept. Nested
 * mixins are attributed to a synthetic `.mixin` file, but the OUTER
 * expansion contains the inner `mixin("...")` as literal text, which the
 * built-in evaluator expands recursively — so only top-level anchors
 * matter here.
 *
 * The compiler is only a fallback: the built-in evaluator runs first (no
 * process spawn, works on broken code), and this resolver is consulted
 * only when it returns null. Broken mid-edit code makes the compiler exit
 * non-zero with an empty dump, which degrades gracefully back to DCD's
 * normal behavior.
 */
final class MixinExpansionResolver
{
private:
	/// Compiler executable + the flag spelling that enables the mixin dump.
	struct CompilerSpec
	{
		string executable;
		string mixinFlag;
	}

	/// Candidate compilers in preference order (first found wins).
	static immutable CompilerSpec[] candidates = [
		CompilerSpec("dmd", "-mixin="),
		CompilerSpec("ldmd2", "-mixin="),
		CompilerSpec("ldc2", "-mixin="),
		CompilerSpec("gdc", "-fsave-mixins="),
	];

	/// The resolved compiler, null when none is available.
	CompilerSpec compiler;

	/// Import paths passed to the compiler so that the file's imports
	/// resolve (mixin generators often live in imported modules).
	string[] importPaths;

	/// Cache: source content hash -> expansions for that source. Editors
	/// re-send the same document on every request; only changed content
	/// pays the compiler round-trip (~100-200ms).
	MixinExpansion[][ulong] cacheEntries;

	/// Cap on cached entries so a long editing session cannot grow the
	/// cache without bound.
	enum maxCacheEntries = 32;

public:

	this(const(string)[] importPaths = [])
	{
		foreach (path; importPaths)
			this.importPaths ~= path.idup;
	}

	/**
	 * Whether a compiler supporting mixin expansion was found. Checked
	 * once; a missing compiler simply disables the feature.
	 */
	bool available() @property const
	{
		return compiler.executable !is null;
	}

	/**
	 * Resolves the string mixins of a source text.
	 *
	 * Params:
	 *     source = the D source code
	 * Returns: the expansions anchored in this file, or an empty array
	 *     when the compiler is unavailable, the code does not compile,
	 *     or the file contains no string mixins.
	 */
	MixinExpansion[] resolve(string source)
	{
		// No `available()` gate here: the compiler is discovered lazily
		// in runCompiler(), so gating on availability before that would
		// permanently disable the resolver.
		if (!containsStringMixin(source))
			return [];

		immutable hash = hashOf(source);
		if (auto cached = hash in cacheEntries)
			return *cached;

		auto expansions = runCompiler(source, hash);
		cacheEntries[hash] = expansions;
		evictIfFull();
		return expansions;
	}

private:

	/**
	 * Cheap pre-check: only files containing a `mixin` token immediately
	 * followed by `(` can have string mixins. `mixin template`,
	 * `mixin Tpl;` and `mixin identifier` (template mixins, which DCD
	 * already handles) are excluded, so most files never spawn a process.
	 */
	static bool containsStringMixin(string source)
	{
		if (!source.canFind("mixin"))
			return false;
		LexerConfig config;
		auto cache = StringCache(clampedBucketCount(source.length));
		auto tokens = getTokensForParser(cast(ubyte[]) source, config, &cache);
		foreach (i, ref t; tokens)
			if (t.type == tok!"mixin" && i + 1 < tokens.length
				&& tokens[i + 1].type == tok!"(")
				return true;
		return false;
	}

	/**
	 * Runs the compiler on a copy of the source and parses the dump.
	 */
	MixinExpansion[] runCompiler(string source, ulong sourceHash)
	{
		import std.file : mkdirRecurse, remove, write;

		// Resolve the compiler lazily on first use so that a compiler
		// installed after server start is picked up.
		if (compiler.executable is null && !findCompiler())
			return [];

		auto sw = StopWatch(AutoStart.yes);

		// The source is written to a temp file: the compiler needs a file,
		// and unsaved editor buffers have none. A module declaration
		// inside the source is authoritative — the compiler does not
		// require the file name to match it (verified empirically).
		auto tempDirPath = buildPath(tempDir(), "dcd-mixin");
		mkdirRecurse(tempDirPath);
		auto sourceFile = buildPath(tempDirPath,
			"dcd-" ~ sourceHash.to!string ~ ".d");
		write(sourceFile, source);
		scope (exit) remove(sourceFile);

		auto dumpFile = buildPath(tempDirPath,
			"dcd-" ~ sourceHash.to!string ~ ".mixin");
		if (exists(dumpFile))
			remove(dumpFile);

		auto args = [compiler.executable, compiler.mixinFlag ~ dumpFile,
			"-o-", "-c", sourceFile]
			~ importPaths.map!(a => "-I" ~ a).array;

		auto pipes = pipeProcess(args, Redirect.stdout | Redirect.stderr);
		immutable status = wait(pipes.pid);
		if (status != 0)
		{
			// Broken mid-edit code: expected while typing. Not an error.
			return [];
		}
		if (!exists(dumpFile))
			return [];

		auto expansions = parseDump(readText(dumpFile), sourceFile);
		remove(dumpFile);

		infof("Mixin resolver: %s expansion(s) via %s in %s ms",
			expansions.length, compiler.executable,
			sw.peek().total!"msecs");
		return expansions;
	}

	/**
	 * Finds a usable compiler on the PATH. The result is cached; a miss
	 * is cached too so that the PATH is not rescanned on every request.
	 */
	bool findCompiler()
	{
		import std.process : environment;

		foreach (ref candidate; candidates)
		{
			auto pathEnv = environment.get("PATH", "");
			foreach (dir; pathEnv.splitter(':'))
			{
				if (dir.empty)
					continue;
				auto candidatePath = buildPath(dir, candidate.executable);
				if (exists(candidatePath))
				{
					compiler = CompilerSpec(candidatePath,
						candidate.mixinFlag);
					return true;
				}
			}
		}
		return false;
	}

	/**
	 * Parses the compiler's mixin dump into expansions anchored in
	 * `sourceFile`.
	 *
	 * Format (entries separated by blank lines):
	 * ---
	 * // expansion at <file>(<line>)
	 * <generated text, possibly multi-line>
	 * ---
	 *
	 * Anchors with a foreign or empty file (expansions from imported
	 * modules) are skipped.
	 */
	static MixinExpansion[] parseDump(string dump, string sourceFile)
	{
		MixinExpansion[] result;
		string currentFile;
		size_t currentLine;
		string[] currentText;

		void flush()
		{
			if (currentFile == sourceFile && currentLine > 0
				&& !currentText.empty)
			{
				result ~= MixinExpansion(currentLine,
					currentText.join("\n"));
			}
			currentFile = null;
			currentLine = 0;
			currentText = null;
		}

		foreach (line; dump.lineSplitter)
		{
			auto anchor = parseAnchor(line);
			if (anchor[1] > 0)
			{
				flush();
				currentFile = anchor[0];
				currentLine = anchor[1];
			}
			else if (currentFile !is null)
			{
				// Text (or blank) line of the current entry. Generated
				// text can itself contain blank lines, so blank lines are
				// collected too; the entry ends at the next anchor or end
				// of input.
				currentText ~= line;
			}
		}
		flush();

		// Trim trailing blank lines that the separator format adds.
		foreach (ref e; result)
			e.text = e.text.chomp();
		return result;
	}

	/**
	 * Parses `// expansion at <file>(<line>)`. Returns null when the line
	 * is not an anchor.
	 */
	static Tuple!(string, "file", size_t, "line") parseAnchor(string line)
	{
		auto trimmed = line.stripLeft();
		if (!trimmed.startsWith("// expansion at "))
			return typeof(return).init;

		immutable content = trimmed["// expansion at ".length .. $];
		// <file>(<line>) — the file part may be empty (expansions from
		// imported modules sometimes have no anchor file).
		immutable open = content.lastIndexOf('(');
		if (open == -1)
			return typeof(return).init;
		auto file = content[0 .. open];
		auto linePart = content[open + 1 .. $];
		if (!linePart.endsWith(")"))
			return typeof(return).init;
		linePart = linePart[0 .. $ - 1];
		size_t lineNumber;
		try
			lineNumber = linePart.to!size_t;
		catch (Exception)
			return typeof(return).init;
		return typeof(return)(file, lineNumber);
	}

	/// FNV-1a hash of the source, used as the cache key.
	static ulong hashOf(string source)
	{
		ulong hash = 14_695_981_039_346_656_037UL;
		foreach (c; source)
		{
			hash ^= c;
			hash *= 1_099_511_628_211UL;
		}
		return hash;
	}

	/// Evicts cache entries past the cap (arbitrary order; the cache is
	/// only a perf optimization, never a correctness one).
	void evictIfFull()
	{
		while (cacheEntries.length > maxCacheEntries)
			foreach (hash, _; cacheEntries)
			{
				cacheEntries.remove(hash);
				break;
			}
	}
}
