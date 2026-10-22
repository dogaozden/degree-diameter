# (8,9): 1092960 vertices (table 1091232)

Table value: 1091232 (Miller–Širáň DS14v2 Table 4 = CombinatoricsWiki, March 2013; the live wiki could not
be read from the container, see research/frontier/TABLE.md). Bipartite Moore bound 13,451,202.

Construction (frontier-opus, 2026-10-22): Haar graph H(G,S) of G = SL(2,23) × Z₄₅ (order 546480): vertices (g,A), (g,B);
edges (g,A) ~ (s g, B), s ∈ S, |S| = 8. 8-regular, sides 546480 + 546480. S is in 1092960-frontier-haar-sl_23_x45.solution.txt (matrices over GF(p),
up to sign for PSL / up to scalars for PGL; meta(a,j) = element (a,j) of Z_m ⋊_r Z_k; z = element of the cyclic factor).
Found by research/frontier/haar_gen.c (annealing over S with targeted moves).
Rebuild: `python3 research/frontier/build_haar.py records/bipartite_dd/d8D9/1092960-frontier-haar-sl_23_x45.solution.txt out.edges.txt`
(re-implements the group independently of the C search; also checks both eccentricities by BFS).

File: 1092960-frontier-haar-sl_23_x45.edges.txt.gz — plain edge list, first line n, then "u v" per line; side A = 0..546479, side B = 546480..1092959.
sha256 of the uncompressed file: e6d47c0c77dc3b66bcbcf78964396de38128a65a8752107df5223b417ee2861e

Checked 2026-10-22 with research-lab/verify/bigcheck (independent checker, BFS from every vertex):
VALID    n=1092960 Delta=8 D=9, diameter 9, total 1809.64 s (research/frontier/runs/bigcheck_d8D9_1092960.txt).
