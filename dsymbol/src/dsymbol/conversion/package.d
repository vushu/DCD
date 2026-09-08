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

module dsymbol.conversion;

import dparse.ast;
import dparse.lexer;
import dparse.parser;
import dparse.rollback_allocator;
import dsymbol.cache_entry;
import dsymbol.conversion.first;
import dsymbol.conversion.second;
import dsymbol.conversion.third;
import dsymbol.mixin_eval : MixinExpansion;
import dsymbol.modulecache;
import dsymbol.scope_;
import dsymbol.semantic;
import dsymbol.string_interning;
import dsymbol.symbol;
import dsymbol.ufcs;
import std.algorithm;
import std.experimental.allocator;
import containers.hashset;

/**
 * Used by autocompletion.
 */
ScopeSymbolPair generateAutocompleteTrees(const(Token)[] tokens,
	RollbackAllocator* parseAllocator,
	size_t cursorPosition, ref ModuleCache cache)
{
	Module m = parseModuleForAutocomplete(tokens, internString("stdin"),
		parseAllocator, cursorPosition);

	scope first = new FirstPass(m, internString("stdin"), &cache);
	// String mixins the built-in evaluator cannot expand are resolved by
	// the external compiler-based resolver, if the server installed one.
	// The in-memory document's text is reconstructed from its tokens.
	if (cache.mixinResolver !is null)
		first.setMixinExpansions(cache.mixinResolver(
			sourceTextOf(tokens)));
	first.run();

	secondPass(first.rootSymbol, first.moduleScope, cache);

	thirdPass(first.rootSymbol, first.moduleScope, cache, cursorPosition);

    auto ufcsSymbols = getUFCSSymbolsForCursor(first.moduleScope, tokens, cursorPosition);

	auto r = move(first.rootSymbol.acSymbol);
	typeid(SemanticSymbol).destroy(first.rootSymbol);
	return ScopeSymbolPair(r, move(first.moduleScope), ufcsSymbols);
}

struct ScopeSymbolPair
{
	void destroy()
	{
		typeid(DSymbol).destroy(symbol);
		typeid(Scope).destroy(scope_);
		// don't destroy ufcsSymbols contents since we don't own the values
		// array itself is GC-allocated, so we just let it live
	}

	DSymbol* symbol;
	Scope* scope_;
	DSymbol*[] ufcsSymbols;
}

/**
 * Used by import symbol caching.
 *
 * Params:
 *     tokens = the tokens that compose the file
 *     fileName = the name of the file being parsed
 *     parseAllocator = the allocator to use for the AST
 * Returns: the parsed module
 */
Module parseModuleSimple(const(Token)[] tokens, string fileName, RollbackAllocator* parseAllocator)
{
	assert (parseAllocator !is null);
	scope parser = new SimpleParser();
	parser.fileName = fileName;
	parser.tokens = tokens;
	parser.messageFunction = &doesNothing;
	parser.allocator = parseAllocator;
	return parser.parseModule();
}

private:

/**
 * Reconstructs the source text of a document from its tokens, for the
 * external mixin resolver (which feeds the text to the D compiler and
 * matches expansions by line number).
 *
 * Two invariants matter, both verified against dparse's token model:
 * $(UL
 *     $(LI Keyword and operator tokens have a $(D null) `text`; their
 *         spelling comes from `str(t.type)` instead.)
 *     $(LI Line numbers must be preserved: the compiler's dump anchors
 *         expansions by line, and FirstPass matches them against
 *         `token.line` of the original document. Each token is emitted
 *         at its own absolute line, and newlines inside multi-line
 *         tokens (e.g. `q{...}`) are accounted for.)
 * )
 * Whitespace within a line is not preserved (a single space separates
 * tokens), which is fine: D is whitespace-insensitive and only line
 * numbers are matched.
 */
string sourceTextOf(const(Token)[] tokens)
{
	import std.array : appender;

	auto buf = appender!string;
	size_t currentLine = 1;
	foreach (ref t; tokens)
	{
		if (t.type == tok!"__EOF__" || t.type == tok!"")
			continue;
		// Emit the token on its own absolute line.
		if (t.line > currentLine)
		{
			foreach (_; currentLine .. t.line)
				buf.put('\n');
			currentLine = t.line;
		}
		immutable text = t.text !is null ? t.text : str(t.type);
		buf.put(text);
		// Multi-line tokens (token strings, block comments) advance the
		// line counter by their embedded newlines.
		foreach (c; text)
			if (c == '\n')
				currentLine++;
		buf.put(' ');
	}
	return buf.data;
}

Module parseModuleForAutocomplete(const(Token)[] tokens, string fileName,
	RollbackAllocator* parseAllocator, size_t cursorPosition)
{
	scope parser = new AutocompleteParser();
	parser.fileName = fileName;
	parser.tokens = tokens;
	parser.messageFunction = &doesNothing;
	parser.allocator = parseAllocator;
	parser.cursorPosition = cursorPosition;
	return parser.parseModule();
}

class AutocompleteParser : Parser
{
	override BlockStatement parseBlockStatement()
	{
		if (!currentIs(tok!"{"))
			return null;
		if (cursorPosition == -1) return super.parseBlockStatement();
		if (current.index > cursorPosition)
		{
			BlockStatement bs = allocator.make!(BlockStatement);
			bs.startLocation = current.index;
			skipBraces();
			bs.endLocation = tokens[index - 1].index;
			return bs;
		}
		immutable start = current.index;
		auto b = setBookmark();
		skipBraces();
		if (tokens[index - 1].index < cursorPosition)
		{
			abandonBookmark(b);
			BlockStatement bs = allocator.make!BlockStatement();
			bs.startLocation = start;
			bs.endLocation = tokens[index - 1].index;
			return bs;
		}
		else
		{
			goToBookmark(b);
			return super.parseBlockStatement();
		}
	}

private:
	size_t cursorPosition;
}

class SimpleParser : Parser
{
	override Unittest parseUnittest()
	{
		expect(tok!"unittest");
		if (currentIs(tok!"{"))
			skipBraces();
		return allocator.make!Unittest;
	}

	override MissingFunctionBody parseMissingFunctionBody()
	{
		// Unlike many of the other parsing functions, it is valid and expected
		// for this one to return `null` on valid code. Returning `null` in
		// this function means that we are looking at a SpecifiedFunctionBody
		// or ShortenedFunctionBody.
		//
		// The super-class will handle re-trying with the correct parsing
		// function.

		const bool needDo = skipContracts();
		if (needDo && moreTokens && (currentIs(tok!"do") || current.text == "body"))
			return null;
		if (currentIs(tok!";"))
			advance();
		else
			return null;
		return allocator.make!MissingFunctionBody;
	}

	override SpecifiedFunctionBody parseSpecifiedFunctionBody()
	{
		if (currentIs(tok!"{"))
			skipBraces();
		else
		{
			skipContracts();
			if (currentIs(tok!"do") || (currentIs(tok!"identifier") && current.text == "body"))
				advance();
			if (currentIs(tok!"{"))
				skipBraces();
		}
		return allocator.make!SpecifiedFunctionBody;
	}

	override ShortenedFunctionBody parseShortenedFunctionBody()
	{
		skipContracts();
		if (currentIs(tok!"=>"))
		{
			while (!currentIs(tok!";") && moreTokens)
			{
				if (currentIs(tok!"{")) // potential function literal
					skipBraces();
				else
					advance();
			}
			if (moreTokens)
				advance();
			return allocator.make!ShortenedFunctionBody;
		}
		else
		{
			return null;
		}
	}

	/**
	 * Skip contracts, and return `true` if the type of contract used requires
	 * that the next token is `do`.
	 */
	private bool skipContracts()
	{
		bool needDo;

		while (true)
		{
			if (currentIs(tok!"in"))
			{
				advance();
				if (currentIs(tok!"{"))
				{
					skipBraces();
					needDo = true;
				}
				if (currentIs(tok!"("))
					skipParens();
			}
			else if (currentIs(tok!"out"))
			{
				advance();
				if (currentIs(tok!"("))
				{
					immutable bool asExpr = peekIs(tok!";")
						|| (peekIs(tok!"identifier")
							&& index + 2 < tokens.length && tokens[index + 2].type == tok!";");
					skipParens();
					if (asExpr)
					{
						needDo = false;
						continue;
					}
				}
				if (currentIs(tok!"{"))
				{
					skipBraces();
					needDo = true;
				}
			}
			else
				break;
		}
		return needDo;
	}
}

void doesNothing(string, size_t, size_t, string, bool) {}
