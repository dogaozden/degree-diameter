# c5 notes: vertex insertion into the 4,970 graph X (card c5)

Setup. X = seeds/valid4970.edges, 4-regular bipartite, A = 0..2484, B = 2485..4969. New a* = 4970 (A side),
b* = 4971 (B side). Any surgery to n = 4,972 is (P, Q, M): a* ~ P (4 B-vertices, or 3 + b*), b* ~ Q (4 A-vertices,
or 3 + a*), and M = matching of deleted X-edges (q, p), q in Q, p in P. Degree preservation forces M to be a
perfect matching of X-edges between Q and P (3 pairs if a* b* is an edge). Left multiplication by G = Z71 x| Z35
is an automorphism of X and acts transitively on A and on B, so v = 0 and w = 2485 are WLOG.

Evaluator: fam.c (fixed degree 4, bit-parallel BFS, same count as tools/score48; checked on best_D1.edges: 775 = 775).
Build: gcc -O2 -march=native -o fam fam.c. Run: ./fam FAMILY BESTFILE [from to].

Families (exhaustive unless noted):
- D1  a* twin of 0 (P = N(0)); b* gets one freed a_i per b_i in N(0): 81 graphs. best far 775.
- D2  b* twin of 2485 (Q = N(2485)); mirror of D1: 81 graphs. best far 794.
- D3  a*b* edge; a* ~ three of N(0) + b*; b* ~ three freed a_i + a*: 108 graphs. best far 217.
- D3m mirror of D3 (b* ~ three of N(2485) + a*): 108 graphs. best far 205.
- D4  both twins, no a*b* edge (P = N(0), Q = N(w), perfect matching between them), all w in B: 0 candidates.
      Reason: only B-vertices w in N(0) or at distance 3 from 0 have any X-edge between N(0) and N(w); w in N(0)
      has 7 such edges but no perfect matching; distance-3 w has exactly 1 edge. Distance 5 (card) is impossible.
- D5  a*b* edge with both twins (three of N(0), three of N(w), perfect 3-matching), all w: 0 candidates (same reason).
- D7  a* ~ three of N(0) + x, x a B vertex at distance 3 from 0 (36 choices); b* ~ freed a_i and a_x: 15,552 graphs
      (chunked by x). best far so far 294 (x chunks 0-24 done), rest see run_D7_*.txt.
- D7m mirror of D7 (b* ~ three of N(2485) + y, d(2485, y) = 3).

Rerun: ./fam D1 best_D1.edges; ./fam D2 best_D2.edges; ./fam D3 best_D3.edges; ./fam D3m best_D3m.edges;
./fam D7 best_D7.edges 0 12 (then 12 24, 24 40 in separate commands; each under 100 s).
Verify a best file: ../../tools/score48 best_X.edges 4 9.

## Structured local families (added after the twin families)

Key identity: for any surgery, P = a* neighbours in B (4, or 3 + b*), Q = b* neighbours in A (4, or 3 + a*), and the
deleted edges must be a perfect matching between Q and P in X (degrees 4 are preserved only that way).

- GEN4 R=1: no a*b* edge; 4-matching with e0 = (0, N(0)[t]) fixed WLOG and the others within distance 1: 2160 graphs, best 162
  (start: (0,4701),(924,3409),(1300,3572),(2429,3381)).
- SWAP round 1 (exhaustive single-edge swaps of the GEN4 best, 4 x 9940): best 154 = best154.edges
  (deleted (0,4701),(924,3409),(1300,3572),(177,4934)). Verified with score48: far = 154.
- SWAP round 2 from 154: no swap below 154 (local minimum).
- GEN3 R=1 (540 graphs) and R=2 (about 10k graphs, index-chunked): best 166.
- SWAP3 round 1 (single swaps of the GEN3 R=2 best, a*b* edge kept): best 149 = best149.edges
  (deleted (0,2485),(2252,3154),(1609,3881); a* ~ 2485,3154,3881,b*; b* ~ 0,2252,1609,a*). Verified with score48: far = 149.
- SWAP3 round 2 from 149: best neighbour 151, so 149 is a local minimum for single swaps.

Commands: START="q1,p1;q2,p2;q3,p3;q4,p4" ./fam SWAP OUT.edges FROM TO (4-matchings) and START=... ./fam SWAP3 OUT FROM TO
(3-matchings with a*b*). Each chunk is under 100 s; the best file is written per process, so chunk files are not merged.
- SWAP3 multi-start from the second GEN3 R=2 design (0,2485;1300,3572;2216,4701; far 166): best neighbour 149 with
  (1926,2864) replacing (0,2485). Different edge set from the first 149; same value (not isomorphism-checked).
