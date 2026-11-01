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
