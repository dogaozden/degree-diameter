# research/lowmem: low-memory orbit Haar search for N ~ 10^9 (job "cell-15-10")

Goal of the job: beat the bipartite (Δ, D) = (15,10) record, 2,300,326,510 vertices (DS14v2 table, 2013), i.e. a Haar
graph H(G,S) with |G| > 1,150,163,255 and |S| = 15. The orbit search of `../structured/haar_sym.c` (branch
claude/structured-search-orbit-w5dd4f) is the method that broke the random-S wall at D = 7..10, but it stores about
11–14 bytes per group element (coset index, 64-bit row tables, bitsets): ~14–17 GB at N = 1.2·10⁹, more than this
16 GB box. `haar_lean.c` runs the same orbit annealing with a different evaluator that stores **two bitsets of N bits
and nothing per element** (0.29–0.31 GB per thread at N = 1.2·10⁹).

## How the evaluator works

G = SL(2,p) × Z_n or PSL(2,p) × Z_n, p prime, gcd(p, n) = 1. Rows are the left cosets of H = U × Z_n with
U = {[[1,t],[0,1]]} (cyclic of order L = pn). The coset of M = [[a,b],[c,d]] is fixed by its first column u = (a,c)
(up to sign for PSL), with representative g_u = [u | v(u)], v(u) = (0, 1/a) or (−1/c, 0); M = g_u U_t with t = b/a or
d/c, and (M, z) is bit CRT(t, z) of row u. Left multiplication by s = (A, z_s) sends row u to row Au and rotates the
row by CRT(t', z_s), where A g_u = g_{Au} U_{t'}. So a BFS level is R × Δ rotated ORs of long rows (R = p² − 1 rows of
pn ≈ 60,000 bits for p ≈ 140), which streams through memory, and the generator tables have only R entries. Sparse
levels push element lists through the same tables. The last level only counts (a row stops when it is full) and
gives up as soon as the count reaches the best candidate of the move (exact).

Speed on this container (Xeon 2.1 GHz, 4 cores; single-core streaming bandwidth ~11–14 GB/s, ~49 GB/s for 4 jobs):
0.9 s per evaluation at N = 1.16·10⁹ (levels 7, 8, 9 are the dense ones, ~0.25 s each), against ~6 s at N = 6.6·10⁸ for
haar_sym FAST=1 (7.5 GB).

## Validation (before any (15,10) run)

- Cost 0 and full diameter check VALID on the record files d8D10_sl_59_19, d8D10_sl_67_13, d10D10_psl_389_1,
  d10D10_sl_79_61 (../frontier/sols).
- Nonzero costs: each record with one generator replaced by a random element (perturb seeds 1–3), cost compared with
  the independent checkers run with header D' = D − 1 (missing count on the target side): identical on 12 of 12
  (SL and PSL, D = 10 and D = 9 with both BFS sides).
- Search: (10,10) SL(2,79) × Z61 (record order, μ = 15.3) solved in 97 evaluations, haarcheck_sl VALID.

## Files

- `haar_lean.c`: the program (usage and environment variables in its header comment). Build:
  `gcc -O3 -march=native -mprefer-vector-width=512 -fopenmp -o haar_lean haar_lean.c -lm`
- `run1.sh SECS SEED FAM P N [VAR=x ...]`: one (15,10) run (nice 5, K = 8), solution to ../frontier/sols/, log to runs/.
- `mu_list.py d D LO HI [k] [NMAX]`: SL/PSL(2,p) × Z_n in an order window with μ = N e^(−W/N).
- `runs/`: logs, and the independent checker outputs (`*.haarcheck2.txt`, `*.haarcheck_sl.txt`).

## (15,10) results (job cell-15-10, 2026-10-24)

All runs: `run1.sh` (k = 3 orbits, m = 5, f = 0; K = 8; defaults otherwise), one thread each, on a box shared with
1–3 other runs, a checker and Haiku squad jobs (so one evaluation took 1–2 s instead of 0.9 s).

| group | N | vertices | vs table | μ | evaluations | wall | check |
|---|---|---|---|---|---|---|---|
| SL(2,139) × Z433 | 1,162,812,840 | 2,325,625,680 | +1.10 % | 5.7 | 17 | 13 s | self OK; haarcheck2 VALID (1,099 s) |
| SL(2,139) × Z457 | 1,227,264,360 | 2,454,528,720 | +6.70 % | 16.4 | 377 | 324 s | self OK |
| SL(2,149) × Z373 | 1,233,809,400 | 2,467,618,800 | +7.27 % | 18.2 | 761 | 863 s | self OK |

(Table updated as runs finish; the logs are in runs/.)

## Second session (2026-10-25): orbits of size 5 on PSL(2,p) × Z_n, FIXPRE

`ORBIT="5 3 0"` (S = 3 orbits of an automorphism of order 5) on PSL(2,p) × Z_n with p ≈ 130–200 and n a prime of a few
hundred, plus `FIXPRE=40`: before each full evaluation an exact meet-in-the-middle test (`fixcheck2`: even ball of
depth 4 from (e,A) keyed by the torus coset invariant (y g y⁻¹, z), odd ball of depth 5 from (e,B) streamed past it)
checks that every α-fixed point is covered, ~0.05 s against ~1.3 s, and redraws the candidate if not. Why k = 5 wins at
(15,10) and what the squad measured: ../squads/cells/d15D10.md. `klist.py d D LO HI k` lists the usable groups.
Other new options: `RANDORB` prints "units" (uncovered α-orbits + uncovered fixed points); `FIXTEST=m` validates
fixcheck/fixcheck2 against the evaluator; `ZMAX` (z-spectrum filter) and `L5DEF` (depth-5 ball deficit filter) exist
but did not pay off.

| group | N | vertices | vs table | μ | evaluations | wall | check |
|---|---|---|---|---|---|---|---|
| SL(2,149) × Z373 (k = 3) | 1,233,809,400 | 2,467,618,800 | +7.27 % | 18.2 | 761 | 863 s | self OK; haarcheck2 VALID (1,072 s) |
| PSL(2,149) × Z761 | 1,258,617,900 | 2,517,235,800 | +9.43 % | 26.4 | 217 | 337 s | self OK |
| PSL(2,181) × Z431 | 1,277,820,180 | 2,555,640,360 | +11.10 % | 35.0 | 217 | 413 s | self OK; haarcheck_psl VALID (2,021 s) |
| SL(2,109) × Z991 | 1,283,265,720 | 2,566,531,440 | +11.57 % | 37.9 | 5,553 | 8,045 s | self OK; haarcheck2 VALID (955 s) |

Not solved (each run sat on a cost-5 plateau, one uncovered α-orbit): PSL(2,139) × Z961 (μ 41.9, +12.19 %) and
PSL(2,151) × Z751 (μ 43.3, +12.40 %), 40,571 evaluations together (11 runs, plateau and restart modes); PSL(2,199) × Z331 (μ 50.8) was dropped
after a screen (median 9 units after FIXPRE, far too few successes expected in the time left).
