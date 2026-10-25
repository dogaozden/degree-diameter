# raise-d13D10: notes for resuming (Haiku worker, 2026-10-25)

Goal: beat our (13,10) record **677,714,400** (SL(2,199) × Z43, Haar, k=3 m=4 f=1, μ = 20.7, 5.6·10³ evals). Table
617,330,936. Moore bound 11,257,702,586. Vertices = 2N, so a new record needs N > 338,857,200.

## Setup facts (measured on this box)

- 4 cores, 15 GB RAM, Xeon AVX-512. Build: `gcc -O3 -march=native -fopenmp -o haar_sym haar_sym.c -lm` in
  research/structured (binaries are not committed). Checkers: `tools/haarcheck_psl` (PSL) and `tools/hcsl`, `tools/hc2`
  (SL, built from ../frontier/haarcheck_sl.c and haarcheck2.c; not committed).
- Memory is the limit, not cores: a wide-row run at N ≈ 3.4·10⁸ holds ~5.0 GB RSS. **Two concurrent runs at most**
  (about 10 GB), not four. `FAST=0` (haar_gen3 evaluation, ~14 B per element) would allow about three, but it is slower.
- Speed: ~0.45 s per evaluation single-threaded at N ≈ 3.4·10⁸ (THREADS=1), measured on the idle box. The
  `plan_orbit.py` law (in branch claude/structured-search-orbit-04hefm, tools/, not in this branch) gives ln(evals) ≈
  5.7 + 0.43·μ_A. μ_A ≈ 8–10 for the rungs below, so 7–10·10³ evals is the expected range (x5 scatter).
- `orbq.sh` is not executable in git: run it with `bash tools/orbq.sh`.

## Candidate rungs (plan_orbit.py, cheapest first, above the record)

| group | 2N | μ | predicted evals |
|---|---|---|---|
| SL(2,131) × Z151 | 678,883,920 | 21.3 | 6.8e3 |
| PSL(2,163) × Z157 | 679,901,688 | 21.9 | 6.8e3 |
| PSL(2,251) × Z43 | 679,959,000 | 21.9 | 7.5e3 |
| SL(2,167) × Z73 | 679,965,216 | 21.9 | 8.1e3 |
| SL(2,97) × Z373 | 680,781,696 | 22.4 | 7.6e3 |
| SL(2,149) × Z103 | 681,406,800 | 22.8 | 9e3 |
| SL(2,101) × Z331 | 681,992,400 | 23.1 | 8.7e3 |
| SL(2,139) × Z127 | 682,111,920 | 23.2 | 9.5e3 |
| SL(2,163) × Z79 | 684,232,272 | 24.5 | 1.2e4 |

Job files: `runs/raise13_10/jobsA.txt`, `runs/raise13_10/jobsB.txt` (orbq.sh format, 5400 s per rung, seed 1). Logs
and solution files: `runs/raise13_10/out/`. A solved rung is checked by the independent checker inside orbq.sh and
the verdict is appended to its log.

Dropped: PSL(2,125) × Z349 (681,597,000; planner lists it). 125 = 5³ is a prime power. haar_sym accepts it, but the
only checker for PSL above 20M (`tools/haarcheck_psl`) is prime-only, so a hit could not be verified. Its job line in
jobsB.txt is a comment now.

## Status

- **Record now 681,406,800** (SL(2,149) × Z103, k=3 m=4 f=1, μ = 22.8, 857 evals, 1,481 s). Solution:
  `research/frontier/sols/d13D10_sl_149_103_orb3_s1.txt`. Checked by haar_sym's full diameter check and by both
  low-memory SL checkers `tools/hcsl` and `tools/hc2` (VALID, 13-regular, simple, ecc 10). Log:
  `research/structured/runs/raise13_10/out/`.
- Before it: PSL(2,251) × Z43, 679,959,000 (`d13D10_psl_251_43_orb3_s1.txt`, 161 evals), VALID by `haarcheck_psl`.
- Earlier the same day: PSL(2,163) × Z157, 679,901,688 (`d13D10_psl_163_157_orb3_s1.txt`, 1,497 evals), also VALID,
  superseded by 251×43.
- 2026-10-25 07:29 UTC: queues A and B started (SL 131×151 and PSL 163×157 first).
- 07:53 UTC: PSL 163×157 solved; queue B moved on to PSL 251×43. 07:56 UTC: SL 131×151 killed (below the new record);
  queue A2 (`jobsA2.txt`: SL 167×73, 97×373, 149×103, 101×331, 139×127) started.
- 08:01 UTC: PSL 251×43 solved and VALID (679,959,000).
- Failed rungs (5,400 s each, best cost): SL 167×73 (1, 3,977 evals), SL 101×331 (3, 10,073), SL 97×373 (1, 9,313),
  SL 163×79 (3, 4,153). Each is a 1.5 h rung, so the budget is short for the larger ones.
- 11:31 UTC: SL 149×103 solved and VALID (681,406,800). Running: PSL 151×199 (queue B), then PSL 211×73.

## Resume

1. `cd research/structured`, build haar_sym and the checkers (above).
2. `THREADS=1 OMP_NUM_THREADS=1 setsid nohup nice -n 5 bash tools/orbq.sh runs/raise13_10/jobsA2.txt runs/raise13_10/out`
   and the same for jobsB.txt (A2 holds the rungs above the current record). Jobs whose log has RESULT are skipped,
   so restarting is safe. Before starting a rung, check that its 2N is above the current record.
3. A solved file goes to `research/frontier/sols/d13D10_<group>_orb3_s<seed>.txt` (copy the solution, keep its log in
   `research/structured/runs/raise13_10/`). Then update the record and the table in this file.
