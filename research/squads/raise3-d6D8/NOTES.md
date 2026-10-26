# raise3-6-8 notes (Haiku worker, round 3 of job "raise-6-8")

Goal: beat the (6,8) bipartite record 31,680 vertices (Haar PSL(2,11) x Z24, 2N with N = 15,840).
Round 2 (branch claude/raise2-6-8-haar-n4stxc) tried k=2/k=3 Haar orbit searches and metacyclic/heis/agl1/PSL
families for N = 15,841..17,000: nothing below cost 3. Its untried route, which this round implements:
**2-fiber bi-Cayley (voltage) lifts**: G = H x Z_n acts regularly on each of 4 fibers (2 per side); V = 4|G|.
|G| >= 7,921 beats the record.

## Files
- mkgroup.py: writes a Mobius group table (PSL(2,q) / PGL(2,q)) as a binary file. Orders are asserted.
- bicay.c (gcc -O3 -march=native -o bicay bicay.c -lm): SA over voltage sets; bit-parallel evaluator. Cost =
  sum over the 4 fiber roots of vertices at distance > D (0 = solution). Usage in the file header.
- verify.py: independent Python checker (explicit graph, structure, 4-root diameter, --full = all-pairs BFS).
  Checked on 2 states: the C cost equals the Python cost (42 = 42, 36 = 36).
- runs/: logs of each run; sols/: solutions (with verification output).

## Model
Block sizes: S00 = S11 = A, S01 = S10 = d - A (A in {1,2,3} for d = 6). Blocks: S[i][j] joins side-0 fiber i to
side-1 fiber j: (g,0,i) ~ (a g, 1, j) for a in S[i][j]; side-1 vertices use a^-1.

## Log
- Calibration (150 s each, 4 parallel, K=1, A=3 unless noted): psl8 x Z14 (|G|=7056, V=28224): best 4.
  psl8 x Z16 (8064): best 40 (A=3), 32 (A=2). pgl7 x Z24 (8064): best 36. No solution in any.
- Symmetric voltage sets (K=2, sigma = inner automorphism of order 2, or z -> -z): much worse. Plateaus at 70-74;
  z -> -z gives 91,560 (nearly disconnected). The C and Python costs agree exactly, so these are real. Dropped.
