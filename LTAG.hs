-- An LTAG grammar consists of:
-- * A finite set of terminal symbols T,
-- * A finite set of non-terminal symbols N, N and T are disjoint,
-- * One of the non-terminal symbols is a starting symbol S \in N,
-- * A set of initial trees I,
--   - Interior nodes have non-terminal symbols,
--   - Frontier nodes have terminal or non-terminal symbols;
--     Non-terminal frontier nodes are marked for substitution.
--     !! Q: can we use the adjoining operation on non-terminal frontier
--           nodes in initial trees? !!
-- * A set of auxiliary trees A,
--   - Interior nodes have non-terminal symbols,
--   - Frontier nodes have terminal or non-terminal symbols;
--     Non-terminal frontier nodes are marked for substitution, apart
--     from one special adjoining node called the foot node.  The foot
--     node has the same label as the root node.
--
-- In a lexicalized LTAG grammar, at least one terminal symbol (the anchor) 
-- must appear at the frontier of all (initial or auxiliary) trees.
--
-- IMPORTANT: note the difference between the two:
-- * Perform lexical insertion -> substitute terminal symbols with lexical items,
-- * Lexicalized grammar -> each tree has at least on terminal frontier node.
--
-- BTW: I \union A is called the set of *elementary* trees.
--
--
-- Other properties of an LTAG grammar:
-- * In elementary trees, we can check a set of properties between terminal nodes.
--   For example, we can enforce (case, number, gender?) agreement between different
--   terminal nodes (in fact this applies to the inserted lexical items).
--   !! Q: does it apply (in some way) to non-terminal nodes? !!
-- * We can also state within an elementary tree a constraint over a particular
--   non-terminal node, for example it is possible to say that the particular node
--   can be substituted only by a transivite (or intransivite) verb, but not by
--   any verb.
