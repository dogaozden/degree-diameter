# w07: which ORBIT split f? (SL(2,191) x Z61, D = 9, Delta = 18, lambda = 17.44, mu = 11.35)

Setup. alpha = conj by [[0,190],[1,190]] (order 3, centralizer K = torus Z_192 containing +-I), z -> 13z (only z = 0 fixed).
f must satisfy f = d - 3m, so at d = 18 only f in {0, 3, 6}; f = 1, 2 need d = 19, 20. Tools: haar_w07 (= haar_big0 plus a
DUMP=<prefix> option that writes every RANDORB sample S; the T file and the raw orbit form <file>.orb).

Predictions (clump model, per side; words of x come in orbits of the symmetry group that fixes x):
- generic x: P(hole) = exp(-lambda), total about mu = 11.35 (no symmetry, independent of f).
- -I: symmetry D4 x Z3 (rotation by 2 letters, reversal-inversion, alpha), orbits of size 24: about exp(-lambda/24 - F/8)
  with F = f(f-1)^7/192 the expected number of words in the fixed letters F (F lies in the abelian K, so these words all
  land in K). f = 0, 1, 2: about 0.48; f = 3: 0.38; f = 6: about 0.
- central c = (+-I, z), z != 0 (120 elements): rotation clumps of 4, about 120 exp(-lambda/4) = 1.5 per side, f-independent.
- torus x in K \ {+-I} (190 elements): alpha clumps of 3 plus F-words: about 190 exp(-lambda/3 - F); 0.57 per side at f = 0,
  0.08 at f = 3, about 0 at f = 6.
So the clump model predicts the f-dependence only in the torus and -I classes (about 1 hole per side at most), and f = 6
should be the best. That prediction failed (see measurements).

Measurements (RANDORB, cost = holes of both sides, 3-4 samples per f; log: f*/randorb*.log):
| f | group orbit | samples (cost) | median | classes of the EVALed holes |
|---|---|---|---|---|
| 0 | "3 6 0" | 24, 42, 14 | 24 | s_2: A -I, B -I, 12 generic |
| 3 | "3 5 3" | 30, 26, 54, 54 | 42 | s_1: A -I, B -I, 24 generic (cost 26) |
| 6 | "3 4 6" | 84, 72, 84 | 84 | s_1: 72 generic (30 A, 42 B), no -I, no torus, no central |
Poisson expectation for generic only: 2 mu = 22.7 per sample.

Findings.
1. The f-dependence is real and monotone in the medians (f 0 < 3 < 6, 24 < 42 < 84), but it is in GENERIC holes: at
   f = 6 the 72 holes are all generic, and the alpha-fixed (torus) holes of the clump model never appear at any f.
   The F-word term (which should help torus and -I) is not what drives the cost.
2. -I is a hole on both sides in both f = 0 and f = 3 samples (4 of 4 sides), in line with the Gamma-24 clump prediction
   (about 0.5 per side); none at f = 6 (F-words of -I help there).
3. Central (+-I, z != 0) holes: none in 6 sides, against about 9 predicted by the rotation-4 clump model. The model
   over-predicts central holes here; the rotation clumps must be effectively larger, or the central words are more numerous.
4. Torus holes: none in 3 samples (predicted 0.57 per side for f = 0).
Caveat: 3-4 samples per f, heavy tails; the f = 6 excess is 3x and the samples do not overlap.

Rule for the director (working, not proven). At (18, 9) on SL(2,191) x Z61, the fewer fixed letters the better: keep f small
(f = 0 "3 6 0" or f = 3 "3 5 3"), and do not use f = 6. The f = 0 / f = 3 gap is within noise. The clump theory for
central and torus classes needs fixing before it is used to choose f.
