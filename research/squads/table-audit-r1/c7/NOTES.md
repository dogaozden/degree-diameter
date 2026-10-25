# c7: structure of the Hafner bipartite graphs (Bond-Delorme family)

Source: research/projects/table-audit/lit/hafner_bipartite/ (read only). Files are 0-based neighbour lists
(mdec3.10 is 1-based). Checked with our own BFS: 4.5, 4.7, 4.8, 6.5, 7.5, 8.5, mdec3.7 are simple,
symmetric, bipartite, regular, with the stated degree and diameter.

## Tools written here
- load.py: parser and property checks (bipartite, regular, diameter).
- auts2.py: all-pairs distances (numpy) and a static BFS-order automorphism search. Too slow (thrashes).
- auts3.py: automorphism search with dynamic ordering (next vertex = unmapped vertex with most mapped
  neighbours, candidates = common neighbourhood of their images, distance-matrix pruning).
  Finds |Aut(4.5)| = 160 in about 10 s.
- aut_4.5.json: the 160 automorphisms of 4.5 as permutations.

## Findings for 4.5 (160 vertices, degree 4, diameter 5)
- Aut has 160 elements. Vertex 0 has 160 distinct images, so Aut acts regularly. The graph is therefore
  a Cayley graph Cay(G, S) of the group G = Aut(4.5), |G| = 160.
- G is non-abelian (sampled commutator test). Element orders: 1:1, 2:31, 4:16, 5:4, 8:80, 10:4, 20:24.
- The connection set S = {g : g(0) in N(0)} has 4 elements, with orders 8, 8, 2, 2. Since the graph is
  bipartite and G is a Cayley group, S consists of elements of the odd coset of an index-2 subgroup,
  so G = H u Hx where H = <S^2> has order 80 (not yet checked).
- The graph is therefore a bi-Cayley graph over an index-2 subgroup of order 80. Labels in the file are
  scrambled and do not reveal the group.

## Findings for 4.8 (1650 vertices, degree 4, diameter 8)
- auts3.py on 4.8 hit its 150 s limit after finding only 9 automorphisms (needs a larger time budget or a
  better search). |Aut| = 825 is therefore not verified here. If |Aut| = 825 acts semiregularly with two
  orbits, the two colour classes are the orbits and the graph is a bi-Cayley graph over G (|G| = 825,
  |G| = 3 * 5^2 * 11), with connection set S of size 4 and edges (0,g) ~ (1, s g).
- Target (4,8) = 2184 would be a bi-Cayley graph over a group of order 1092 = 2^2 * 3 * 7 * 13. This needs a
  group of that order with 4 connection elements. No group library is installed (no GAP, no networkx,
  no pynauty), so groups were not searched.

## Construction (as far as found)
Bond-Delorme-style graphs here are Cayley graphs (4.5) or bi-Cayley graphs (4.8) over a moderately sized
non-abelian group G, with a small connection set S of mixed-order elements. The order is |G| for a Cayley
graph of a bipartite group, or 2|G| for a bi-Cayley graph with two colour classes.

## Next steps
1. Recover G and S for 4.8 (orbit of the semiregular group) and for 4.5 (the regular group, in a
   presentation form such as Z_8 x| ...). Then build the same family at (4,8) with |G| = 1092 by trying
   semidirect products Z_m x| Z_n with 4 elements of mixed order, and score with apsp.
2. Use the scorer, not diameter reasoning, to check each candidate.
