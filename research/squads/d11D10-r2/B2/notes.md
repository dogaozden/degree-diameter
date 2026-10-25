# B2: speed of one k = 10 RANDORB sample (psl 243 x Z11)

**Result.** On the shared machine one sample takes 0.42 to 0.52 s (not the 0.37 s on the card). About 43 % is the
10 table builds (22.5 ms each) and 57 % is the BFS (dense levels 6-8 about 72 ms each). The fastest setting with an
identical cost sequence is `HUGEPG=1 FAST=2 PFD=8` (default wide rows, cyclic H of order 122): 417 ms per sample,
about 10 % faster than the unmodified haar_sym (467 ms) in the same sweep. Every setting gives the same costs.

## Code
`haar_sym_B2.c` = research/structured/haar_sym.c (copied 12:49) plus:
1. `ORBPROF=1`: timers for random_orbit, the mktab calls, cost_any and the BFS levels (TIMING=1).
2. `SEQ=1` prints each sample cost; the VARIANT line prints `seqhash` (FNV-1a over the cost sequence).
3. `PFDLIST="p1 p2 .."` reruns the same 30 samples (RNG reset) once per prefetch distance PFD.
4. `HUGEPG=1`: POS, POSW, IDXK, zero_s and the big bitsets are 2 MB aligned with madvise(MADV_HUGEPAGE)
   (THP is in madvise mode on this machine).
Build: `gcc -O3 -march=native -fopenmp -o haar_sym_B2 haar_sym_B2.c -lm` (binary `haar_sym_B2` in this folder).

## Commands (sweep.sh, one gate slot, 13:03:10 to 13:06:44 = 214 s = 3.6 slot-min)
Common: `env -u THREADS ORBIT="10 1 1" AFROB=1 AFROBH="0 1 2 0" AR=2 RANDORB=30 ...` with args `11 10 600 5 8 /dev/null psl 243 11`
(seed 5, N = 78,917,652, mu = 60.61).
- P1 (p1_fast2_pfd.log): ORBPROF=1 SEQ=1 PFDLIST="8 0 4 16 32" FAST=2
- P3 (p3_hugepg.log): ORBPROF=1 SEQ=1 PFDLIST="8 16" HUGEPG=1 FAST=2
- P2 (p2_fast1.log): ORBPROF=1 SEQ=1 FAST=1 (narrow rows, nH = 61)
- P4 (p4_original.log): unmodified research/structured/haar_sym, FAST=2

## Timings (ms per sample, mean of 30 samples)
| run | setting | ms/sample | 10 tables (ms each) | cost_any (BFS) | BFS levels 6 / 7 / 8 | level 9 |
|---|---|---|---|---|---|---|
| P1 | FAST=2 PFD=8 | 519 | 225 (22.5) | 294 | 72 / 72 / 70 | 50 |
| P1 | FAST=2 PFD=0 | 659 | 224 (22.4) | 434 | 107 / 106 / 98 | 94 |
| P1 | FAST=2 PFD=4 | 454 | 199 (19.9) | 256 | 59 / 60 / 59 | 50 |
| P1 | FAST=2 PFD=16 | 450 | 205 (20.5) | 245 | 59 / 57 / 58 | 44 |
| P1 | FAST=2 PFD=32 | 482 | 211 (21.1) | 271 | 65 / 66 / 64 | 48 |
| P3 | FAST=2 PFD=8 HUGEPG=1 | **417** | 168 (16.8) | 248 | 58 / 58 / 58 | 46 |
| P3 | FAST=2 PFD=16 HUGEPG=1 | 434 | 173 (17.3) | 261 | 62 / 61 / 62 | 49 |
| P2 | FAST=1 (narrow) | 1208 | 912 (91.2) | 296 | 67 / 67 / 66 | 80 |
| P4 | unmodified haar_sym, FAST=2 | 467 | - | - | - | - |

Setup: group 2.1 to 3.9 s; wide rows 4.3 to 7.9 s (HUGEPG adds about 4 s, once per process).

## Where one sample spends its time (P1, PFD=8, 519 ms)
- random_orbit: 0.04 ms.
- 10 table builds: 225 ms (22.5 ms each; make_tables_w is bound by random reads of POSW (316 MB) and IDXK (57 MB)).
- BFS (cost_any): 294 ms. Levels 1 to 4 about 2 ms, level 5 12 ms, levels 6 to 8 about 72 ms each (dense pulls over
  646,866 rows x 11 generators), level 9 50 ms.

## Knobs
- **FAST=2 vs FAST=1:** FAST=1 (narrow rows, H = 61 from HMAX=63) is 2.6x slower (1208 ms). Its table builder costs
  91 ms each, since it is not software-pipelined. Keep FAST=2.
- **HWMIN / HWMAX:** the default already selects cyclic H of order 122, which is the largest possible cyclic subgroup
  order <= 256 in PSL(2,243) x Z11. Element orders are divisors of 121, 122 and 3 times the Z11 part; 1342 = 2 * 11 * 61
  gives 122, and no element of order 242, 244 or 256 exists. Nothing to gain.
- **HMAX:** only affects FAST=1 (nH = 61). Not used.
- **PFD:** PFD=0 costs +50 % per sample (BFS 434 vs 294 ms), so prefetch is needed. PFD 4, 8 and 16 are equal within noise
  (450 to 520 ms). PFD=32 is slightly slower. Keep the default 8.
- **HUGEPG=1:** table builds 22.5 to 16.8 ms (about -25 %). Sample 417 ms vs 450 to 520 ms without. The BFS gain is not
  clearly visible in these runs.

## Identical costs
All 9 runs (270 samples) give seqhash bf05356a9ba51e6e (FAST 1 and 2, PFD 0/4/8/16/32, HUGEPG 0 and 1). The summary
(min 22, p1 22, p10 51, median 100, mean 9,565,868.57, var, hist, cost0 = 0 of 30) equals the unmodified haar_sym (P4).
5 of 30 samples are degenerate (cost/k >= 31), in line with A2.

## Caveats
- Shared machine: five haar_sym processes ran during the sweep, so absolute times are 25 to 40 % above the card's 0.37 s.
  Noise between runs is about 10 %.
- Not done: THREADS (out of scope), any search, checkers (no solution was produced).
- Untested idea: the cost is dominated by 10 table builds and dense BFS levels. Halving the table work needs a change of
  formulation (e.g. reuse of the coset map across orbit elements), not a knob.
