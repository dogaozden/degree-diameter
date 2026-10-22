# (7,8): 82,992 vertices (table 80,940)

Table value: 80,940 (Miller–Širáň DS14v2 Table 4 = CombinatoricsWiki, March 2013; the live wiki could not be read
from the container, see research/frontier/TABLE.md). Moore bound 671,846.

Construction (frontier-opus, 2026-10-22): the Haar graph H(G,S) of G = SL(2,13) × Z₁₉ (order 41,496):
vertices (g,A), (g,B), g ∈ G; edges (g,A) ~ (s g, B) for s ∈ S. 7-regular, sides 41,496 + 41,496, 290,472 edges.
S (matrix [[a,b],[c,d]] over GF(13), element of Z₁₉), written (a,b,c,d; z):
(1,0,0,1; 0), (11,2,0,6; 12), (9,0,11,3; 2), (0,10,9,12; 15), (1,5,12,9; 9), (2,9,5,10; 17), (3,1,0,9; 12).
Found by research/frontier/haar_gen.c (annealing over S with targeted moves; 147 s, seed 1).
Rebuild: `python3 research/frontier/build_haar.py records/bipartite_dd/d7D8/82992-frontier-haar-sl2_13xZ19.solution.txt out.edges.txt`
(the builder re-implements the group independently of the C search and also checks both eccentricities by BFS).

File: 82992-frontier-haar-sl2_13xZ19.edges.txt.gz — plain edge list, first line n, then "u v" per line;
vertex g of side A is its index i in the builder's element order, (g,B) is 41496 + i.
sha256 of the uncompressed file: 8c75bcaa77fabcc70791a461fe0a923ecc808a23f31561aca2bba2a8f0beaadb

Checked 2026-10-22 with research-lab/verify/bigcheck (independent checker, BFS from every vertex):
VALID — simple, 7-regular, bipartite (41496 / 41496), connected, exact diameter 8
(research/frontier/runs/bigcheck_d7D8_82992.txt). Too large for scripts/verify_record.py.
