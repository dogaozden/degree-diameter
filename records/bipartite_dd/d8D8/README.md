# (8,8): 206,448 vertices (table 201,480)

Table value: 201,480 (Miller–Širáň DS14v2 Table 4 = CombinatoricsWiki, March 2013; the live wiki could not be read
from the container, see research/frontier/TABLE.md). Moore bound 1,921,600.

Construction (frontier-opus, 2026-10-22): Haar graph H(G,S) of G = PSL(2,23) × Z₁₇ (order 103,224): vertices
(g,A), (g,B); edges (g,A) ~ (s g, B), s ∈ S. 8-regular, sides 103,224 + 103,224, 825,792 edges. S is in
206448-frontier-haar-psl2_23xZ17.solution.txt (matrix over GF(23) up to sign, element of Z₁₇). Found by research/frontier/haar_gen.c in 8 s.
Rebuild: `python3 research/frontier/build_haar.py records/bipartite_dd/d8D8/206448-frontier-haar-psl2_23xZ17.solution.txt out.edges.txt`.

File: 206448-frontier-haar-psl2_23xZ17.edges.txt.gz — plain edge list, first line n, then "u v" per line.
sha256 of the uncompressed file: ca16b01c0b26fd1943f5c728f7a0f3f0f76db7bad21a9dc161a589785dca25ce

Checked 2026-10-22 with research-lab/verify/bigcheck (BFS from every vertex): VALID — simple, 8-regular, bipartite,
connected, exact diameter 8 (research/frontier/runs/bigcheck_d8D8_206448.txt).
