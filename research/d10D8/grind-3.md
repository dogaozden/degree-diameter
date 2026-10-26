# d10D8 grind-3: four orbit-search descents, 6 hours (2026-10-26)

Job: pure compute run of the (10,8) orbit search (`sym2/haar_sym2`, built with `gcc -O3 -march=native -fopenmp`),
no method change, no new code. Base: `claude/bipartite-10-8-cell-um2c1t`. Settings for all four:
`ORBIT="3 3 1" RESTARTAFTER=0 COOL=15 REHEAT=30 ORBW=3`, one core each, 16:59 to 22:54 UTC.

| run | seed | group | descents finished | lowest chain min | last cost seen |
|-----|------|-------|-------------------|------------------|----------------|
| g3a | 3001 | psl 23 97 | 467 | 6 | 27 |
| g3b | 3002 | prod psl 7 sl 8 7 | 466 | 9 | 22 |
| g3c | 3003 | psl 23 97 | 468 | 6 | 19 |
| g3d | 3004 | prod psl 7 sl 8 7 | 464 | 9 | 42 |

Totals: 1,865 descents in about 23.7 CPU-hours. At the cell notes' rate of 2.5e-4 per descent, that is 0.47 expected
solutions, and zero found has probability about e^-0.47 = 0.62. So this run neither confirms nor rules out that rate.
No run died, so no restarts were needed.

## Result

No solution. No run reached cost 0, and no `runs/g3?.txt` or "cost 0"/"SOLVED" line appeared. `verify.sh` was not run,
because there was nothing to verify.

The runs were stopped at 22:54 UTC, at the 6-hour limit, with `pkill`. Their checkpoints `runs/g3?.ckpt` are kept
locally (not committed). Each run resumes from its checkpoint with `launch.sh` and the same tag.

## Files

- `runs/g3?.log`: progress logs with the CHAIN lines, committed at 30-minute intervals.
- `runs/g3?.out`: empty. The RESULT line is written only at a normal exit, and the runs were killed.
