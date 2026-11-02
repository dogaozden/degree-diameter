# h16: quotient / ball statistics as a filter for Sidon S on Z1453 x|_11 Z33 (5,10) and Z6397 x|_5330 Z41 (6,10)

Code: hs.c (copy of r3/g03/hmeta_sidon.c plus SAMPLE statistics mode, FILTK/FSLACK candidate filter, ballsizes).
Build: gcc -O3 -march=native -fopenmp -o hs hs.c -lm. All runs THREADS=1, one at a time, <= 80 s program time.

## 1. Measurement (samp2.txt, corr2.py): 200 random Sidon S, cost = holes after 9 steps (side A), N = 47,949
Median cost 44, mean 50.2, range 13..300.
Spearman with cost (statistic computed from S alone, before the BFS to depth 9):
- B_5 (distinct elements within radius 5, side A): -0.68   (B_4: -0.61, B_6: -0.76, B_7: -0.85, B_8: -0.91)
- wmin (min over fibres j of the number of alternating length-9 words in Z_33): -0.18
- e4 (collision energy of length-4 quotient words): +0.18
- |Delta + Delta| (sums of two differences of the j-coordinates): constant 33, no information
- reach9 (fibres reached by length-9 words): constant 33, no information
- Per-fibre holes (samp1.txt): holes sit in ~20 of the 33 fibres, at most 5 per fibre (typically 1..5), so the
  "one hole per fibre" picture of r2/e14 is not what random Sidon S show here; the quotient statistics do not explain the
  cost (corr.py: wmin and e4 are weak). B_5 is the best cheap predictor found, but it is a group-level statistic, not a
  quotient one.

## 2. Use as a filter in the annealing (hs, env FILTK=k, FSLACK=s)
A candidate replacing generator i is dropped before the full 9-step evaluation unless B_k(candidate) >= B_k(current S) - s.
Filtering keeps 1-10 % of candidates (filtered 64-65k of 65-70k per 80 s), so about 7-8k full evaluations versus 46-47k.
Results (80 s each, K = 24 candidates, Sidon constraint on):
| run | filter | seed | best cost |
|---|---|---|---|
| base11 | none | 11 | 5 |
| filt11 | B_5, slack 0 | 11 | 3 |
| filt12 | B_5, slack 0 | 12 | 4 |
| base12 | none | 12 | 3 |
| chainA | B_5, slack 0, from filt11 (cost 3) | 21 | 3 (no gain) |
| chainB | B_5, slack 60, from filt11 | 22 | 3 (no gain) |
| f6s13 | B_6, slack 0 | 13 | 7 |
Filtered and unfiltered are indistinguishable at this budget (3 vs 5, 4 vs 3). The best state is cost 3 (filt11.sol.best,
re-checked with EVAL). No solve, no raise.

## 3. (6,10) Z6397 x|_5330 Z41 (d = 6), starting from the r2/e08 cost-1 state s102.sol.best (copy d6start.sol)
d6chain (B_5, slack 0): 6,403 full evals, stays at cost 1. d6chainB (B_5, slack 60): 11,346 evals, stays at cost 1.
Note: SIDON was off here; the r2 start state was not checked for the Sidon condition (for d = 6 it needs k >= 31, and k = 41 allows it).

## Read
- B_5 at radius 5 is a real predictor of the random-S cost (rho about -0.7), but the annealing gains nothing measurable
  from filtering at 80 s chains. The filter speeds up evaluation about 6x; the search itself is not better.
- The quotient-level statistics the card proposed (walk counts per fibre, sumset of differences) carry little signal.
- Next: use B_5 as the objective-side tie-breaker (not a hard filter) in long chains, or search over S with
  B_5 as the target at a fixed budget and only then run the full evaluation.

## 4. Control
chainC: unfiltered Sidon chain from the same cost-3 state (filt11.sol.best), 51,150 evals, stays at cost 3. So the filter does not
change the plateau at cost 3 either way.
