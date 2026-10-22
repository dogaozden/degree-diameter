# (6,10): 461472 vertices (table 452032)

Table value: 452032 (Miller–Širáň DS14v2 Table 4 = CombinatoricsWiki, March 2013; the live wiki could not
be read from the container, see research/frontier/TABLE.md). Bipartite Moore bound 4,882,812.

Construction (frontier-opus, 2026-10-22): Haar graph H(G,S) of G = PSL(2,23) × Z₃₈ (order 230736): vertices (g,A), (g,B);
edges (g,A) ~ (s g, B), s ∈ S, |S| = 6. 6-regular, sides 230736 + 230736. S is in 461472-frontier-haar-psl_23_x38.solution.txt (matrices over GF(p),
up to sign for PSL / up to scalars for PGL; meta(a,j) = element (a,j) of Z_m ⋊_r Z_k; z = element of the cyclic factor).
Found by research/frontier/haar_gen.c (annealing over S with targeted moves).
Rebuild: `python3 research/frontier/build_haar.py records/bipartite_dd/d6D10/461472-frontier-haar-psl_23_x38.solution.txt out.edges.txt`
(re-implements the group independently of the C search; also checks both eccentricities by BFS).

File: 461472-frontier-haar-psl_23_x38.edges.txt.gz — plain edge list, first line n, then "u v" per line; side A = 0..230735, side B = 230736..461471.
sha256 of the uncompressed file: c5289950ed618be73d958d159feb12a3fbeb562e0ec16756ce1f2b6483f36b06

Checked 2026-10-22 with research-lab/verify/bigcheck (independent checker, BFS from every vertex):
VALID    n=461472 Delta=6 D=10, diameter 10, total 217.27 s (research/frontier/runs/bigcheck_d6D10_461472.txt).
