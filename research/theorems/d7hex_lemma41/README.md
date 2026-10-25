# Direct checks of Lemma 4.1 and of the duality construction (D7_HEXAGON.md; job thm-d7, 2026-10-25)

Lemma 4.1: if F is a segment set of points of H(q) (every point of F has its collinear F-points on one line), then for
all elements u, v there is a point p not in F with d(u,p) + d(p,v) <= 6 (d = distance in the incidence graph).

`lem41.c` checks this for every ordered pair (u, v) of the 2N elements (bucket BFS from all p not in F, initial label
d(u,p)), for:
- the point set of a greedy (random, maximal) partial spread;
- three random maximal segment sets (random order, add a point when the segment property still holds everywhere);
- a random maximal (R1) set (every point collinear with at most one other point of the set);
- the same families for line sets (the lemma in the dual hexagon H^D);
- a negative control: each random maximal segment set plus one point that creates a turning path (expected to fail).

The hexagon comes from the lab's generator research/d10D7/hexgen2.c (independent of the coordinates code in
research/theorems/d7hex_tests/, which checks Tits' equations separately).

Run (about 15 s for q = 5):

    gcc -O2 -o hexgen2 research/d10D7/hexgen2.c && mkdir -p hex && ./hexgen2 3 && ./hexgen2 4 && ./hexgen2 5
    gcc -O2 -o lem41 research/theorems/d7hex_lemma41/lem41.c
    ./lem41 hex/hex_q3.bin 1; ./lem41 hex/hex_q4.bin 2; ./lem41 hex/hex_q5.bin 3

Result (lem41_q345.out): 0 failing pairs for every segment set and (R1) set, points and lines, q = 3, 4, 5; every
negative control fails (36 to 320 ordered pairs).

## Duality test (Corollary 8.2 at q = 3): dual_test.py, dual_q3.log

All levels of type H, every transition matched by a duality phi, and all (q+1)(q^3+1) = 112 points of the Hermitian
spread of H(3) freed on every transition (main graph, no hubs). phi from the lab's research/d10D7/dual/dualfind.c (at
q = 3 it finds a polarity; dual_test.py re-checks that phi preserves all incidences); the spread is the set of H(3)-lines
in the hyperplane x0 = x4 + x3 (28 lines, pairwise opposite, checked by BFS).

    gcc -O2 -o dualfind research/d10D7/dual/dualfind.c && ./dualfind hex/hex_q3.bin d3
    python3 research/theorems/d7hex_lemma41/dual_test.py hex/hex_q3.bin d3.phi 1 r1.edges && ./apsp_mt r1.edges 5 7 4
    python3 research/theorems/d7hex_lemma41/dual_test.py hex/hex_q3.bin d3.phi 2 r2.edges && ./apsp_mt r2.edges 6 7 4

Results: r = 1 (3 levels, n = 2,184): RESULT VALID d=5 D=7; r = 2 (5 levels, n = 3,640): RESULT VALID d=6 D=7. Negative
control (one more point freed, collinear with a spread point off its spread line): diameter 8, RESULT INVALID.
