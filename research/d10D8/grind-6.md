# grind-10-8-6: final notes (no solution)

Job: four more fresh orbit-search descents for the (10,8) cell, same method and options as grind-10-8-1..4
(`RESTARTAFTER=0 COOL=15 REHEAT=30 ORBW=3`, `ORBIT="3 3 1"`, binary `sym2/haar_sym2` built from `haar_sym2.c`).

## What ran

- **Batch 1** (tags g6a–g6d, seeds 6001–6004; groups `psl 23 97` on a and c, `prod psl 7 sl 8 7` on b and d).
  Started 23:18 UTC. Stopped at the container restart near 23:47 (the logs end at t=1740 s). 150 finished chains.
- **Batch 2** (tags g6e–g6h, seeds 6005–6008; same groups in the same order). Started 23:48 UTC after the restart.
  Alive at the 04:25 checkpoint. Found dead at the 05:00 check, after the worker restart reported in the last turn; the
  exact time of death is not recorded. 1,587 finished chains.
- Total: **1,737 finished chains** (fresh descents), plus the unfinished chains in progress when each batch stopped.

## Lowest costs seen

The `CHAIN` line reports the minimum of the ORBW=3 energy (uncovered elements weighted 3), not the raw uncovered count:

| minimum energy | chains |
|---|---|
| 6 | 1 (g6e) |
| 9 | 14 |
| 12 | 61 |
| 15 | 243 |
| 18 | 465 |

Batch 1 chain minima: g6a 12, g6b 12, g6c 9, g6d 12. No chain reached energy 0 or raw cost 0.

## Solutions

None. No `runs/g6?.txt` was written, no `cost 0` or `SOLVED` line appeared in any log, and no `verify.sh` run was needed.

## Notes

- Batch 1 was lost to the first worker restart, and batch 2 to the second. Each restart killed the processes without a
  clean stop. The checkpoints (`runs/g6?.ckpt`) were committed for the record.
- Batch 2 used fresh tags, so no earlier checkpoint was resumed. Seeds 6005–6008 were the next unused seeds, per the spec.
- Expected cost at 2.5e-4 per descent was about 4,000 descents for one success. About 1,737 finished chains is roughly
  0.4 of that expectation, so the run was too short to say much either way; the best energy stayed at 6 or above.
