# c4 (round1, deep-65b): hubk k = 3 on SmallGroup(258,3), (258,4), (258,5)

Start 23:08 UTC, stop 23:55 UTC (time box 60 min). Family: Haar degree 5 + hubs of size 3 + hub graph of degree 3,
n = 2*258 + 2*86 = 688. Exact search of hubk.c (copied from shared/hubk.c; my copy hubk.c adds chunking, see below).

## Setup and validation
- Tables: `mkdir -p tabs; ../../shared/gapw -c 'ORDER:=258; OUTDIR:="tabs"; IDS:=[3,4,5];' ../../shared/gap_tables.g`
  -> tabs/sg_258_{3,4,5}.txt (names: C43 x S3; C3 x D86; D258).
- Build: `gcc -O3 -march=native -o hubk hubk.c -lm`; `hubk_orig` = unmodified shared/hubk.c build.
- Validation: `./hubk tabs/sg_258_{3,4,5}.txt 3 rand 200 1` -> 200 trials, 0 mismatches, 0 all-zero on each group.
- Leaf counts (`COUNT=1 ./hubk_orig TABLE 3 ex`, exact number of 5-set leaves before any test):
  258_3: 1190 R-orbits, 3,705,385,183,780 leaves; 258_4 and 258_5: 175 R-orbits, 74,737,367,936 leaves each.

## Chunking (my hubk.c)
- Work unit = (qi, PROC): R-orbit ro = qi*397 mod nRo (permutation; spreads the sample), split PROC of NPROC=256 on
  the second element index (exact partition: every leaf in exactly one PROC).
- Env: QS, PS (start cursor), TLIM (seconds budget, stops before the next chunk and prints "STOP qi X proc Y").
- Driver: `sh run_chunks.sh tabs/sg_258_N.txt rN` (TLIM default 85 s, cursor rN.cur, logs rN.log). One call per
  command, no background processes, each under 105 s.
- Checks: order-60 group sg_60_5 (k=3): full run leaves 1398774, pass(3)(6) 793450, pass(2)(5) 781979, solutions
  610895, best 0; chunked (NPROC=7) sums are identical; a stop at TLIM=1.0 and resume from the cursor give identical sums.

## Results (run until 23:55 UTC)
| group | R-orbits | leaves done / total | full R-orbits done | pass (3)(6) | solutions |
|---|---|---|---|---|---|
| 258_3 | 1190 | 3.35e9 / 3.71e12 (0.09%) | 1 (+1 partial) | 0 | 0 |
| 258_4 | 175 | 8.99e9 / 7.47e10 (12.0%) | 18 (+1 partial) | 0 | 0 |
| 258_5 | 175 | 4.82e9 / 7.47e10 (6.4%) | 8 (+1 partial) | 0 | 0 |

- No leaf of any chunk passed the (3)(6) gate, so no leaf reached the cost stage: no "best missing count" exists
  (the program prints 1073741824 as the chunk minimum). Total leaves tested: about 1.7e10, 0 passes.
- Rate on this shared machine: 5e6 to 1.3e7 leaves per second, about 6e6 on average.
- Estimated full runs (single thread): 258_3 about 170 h (roughly 7 days); 258_4 and 258_5 about 2 to 4 h each.
- Not claimed: no solution and no exhaustive result for any of the three groups.

## Next
- A full run on 258_4 and 258_5 is feasible (2 to 4 h each, several processes not allowed by the single-thread rule,
  so split across cursors in sequence). 258_3 needs pruning first.
- The (3)(6) gate is never passed in the sampled R-orbits. A cheap necessary test per R-orbit (for instance, the gate
  count of the best S over a few random samples) would tell whether whole R-orbits can be dropped.
