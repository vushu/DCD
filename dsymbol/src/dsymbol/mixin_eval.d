module dsymbol.mixin_eval;
import dparse.ast;
import dparse.lexer;
import dparse.parser;
import dparse.rollback_allocator;
import dsymbol.conversion : parseModuleSimple;
import dsymbol.scope_;
import dsymbol.modulecache;
import std.string : empty;

Declaration[] parseGeneratedDeclarations(string generated, size_t mixinOffset)
{
	if (generated.empty)
	{
		return [];
	}
	// Pad so token indexes are absolute file offsets.
    auto padded = new char[mixinOffset + generated.length];
    padded[0 .. mixinOffset] = ' ';
    padded[mixinOffset .. $] = generated;

	LexerConfig config;
	config.fileName = "";
	auto stringCache = StringCache(padded.length.optimalBucketCount);
	auto tokens = getTokensForParser(cast(ubyte[]) padded, config, &stringCache);
	if (tokens.empty)
		return [];

	RollbackAllocator rba;
	Module m = parseModuleSimple(tokens[], "", &rba);
	if (m is null || m.declarations.empty)
		return [];
	return m.declarations;

}

string evaluateMixinString(const MixinExpression expr, Scope* sc, ModuleCache* cache)
{
    return null;
}
