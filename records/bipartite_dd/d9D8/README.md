# (9,8): 453840 vertices (table 449480)

Table value: 449480 (Miller–Širáň DS14v2 Table 4 = CombinatoricsWiki, March 2013; the live wiki could not
be read from the container, see research/frontier/TABLE.md). Bipartite Moore bound 4,793,490.

Construction (frontier-opus, 2026-10-22): Haar graph H(G,S) of G = PGL(2,61) (order 226920): vertices (g,A), (g,B);
edges (g,A) ~ (s g, B), s ∈ S, |S| = 9. 9-regular, sides 226920 + 226920. S is in 453840-frontier-haar-pgl_61_x1.solution.txt (matrices over GF(p),
up to sign for PSL / up to scalars for PGL; meta(a,j) = element (a,j) of Z_m ⋊_r Z_k; z = element of the cyclic factor).
Found by research/frontier/haar_gen.c (annealing over S with targeted moves).
Rebuild: `python3 research/frontier/build_haar.py records/bipartite_dd/d9D8/453840-frontier-haar-pgl_61_x1.solution.txt out.edges.txt`
(re-implements the group independently of the C search; also checks both eccentricities by BFS).

File: 453840-frontier-haar-pgl_61_x1.edges.txt.gz — plain edge list, first line n, then "u v" per line; side A = 0..226919, side B = 226920..453839.
sha256 of the uncompressed file: 3a41fde53bcb3b1122cddd17ab36f5113a385979bc78cd23279147ed120f3e8b

Checked 2026-10-22 with research-lab/verify/bigcheck (independent checker, BFS from every vertex):
VALID    n=453840 Delta=9 D=8, diameter 8, total 320.61 s (research/frontier/runs/bigcheck_d9D8_453840.txt).
