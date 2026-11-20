# (10, 8): 1,185,408 vertices (16 November 2026)

Haar graph H(G, S) of G = PSL(2,7) × SL(2,8) × Z₇ (|G| = 592,704) with ten generators (`generators.txt`): vertices (g, 0) and (g, 1),
with (g, 0) adjacent to (g·s, 1) for s in S. Bipartite, 10-regular. The Combinatorics Wiki bipartite table has 1,176,480 at this cell.

    python3 gen.py row out.bin           # builds the graph from the groups, 47 MB
    cc -O2 -fopenmp -o bfs bfs.c && ./bfs out.bin 400

`bfs` checks the graph is simple, 10-regular, symmetric and bipartite, then runs BFS from both sides and from 400 further random vertices
(eccentricity 8 from all, nothing unreached). All vertices are equivalent under left translation by G, so one BFS per side covers every source.
`bfs-output.txt` is the output of the check. SHA-256 of the 47 MB edge list from `gen.py row`: 17cec9076b28bccec4258738dc7f4115f742e20d2e2484d4be4047baa8ce3ae1.
