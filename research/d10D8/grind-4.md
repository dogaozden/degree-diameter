# grind-10-8-4: six-hour orbit-search grind for a (10,8) cost-0 state

Run window: 2026-10-26, 16:59 to 22:58 UTC (about 6 hours). Method unchanged from `../squads/cells/d10D8.md` §8.7 and §9:
`sym2/haar_sym2` built with `gcc -O3 -march=native -fopenmp`, `launch.sh` with `RESTARTAFTER=0 COOL=15 REHEAT=30 ORBW=3`,
ORBIT="3 3 1", one run per core.

## Runs

| run  | group            | seed | chains | lowest chain minimum |
|------|------------------|------|--------|----------------------|
| g4a  | psl 23 97        | 4001 | 460    | 3 (one unit)         |
| g4b  | prod psl 7 sl 8 7 | 4002 | 474    | 6                    |
| g4c  | psl 23 97        | 4003 | 461    | 6                    |
| g4d  | prod psl 7 sl 8 7 | 4004 | 470    | 9                    |

Total: 1865 fresh descents (chains), about 85,800 s of chain time (about 24 CPU-hours on 4 cores, 46 s per chain),
about 173 million evaluations. No run restarted; none died.

Distribution of chain minima (cost: count): 3: 1, 6: 2, 9: 11, 12: 66, 15: 255, 18: 546, 21: 648, 24: 304, 27: 32.

## Lowest costs seen

- **Cost 3** (one uncovered α-fixed element in ORBW=3 units): g4a, chain 323, psl 23 97, seed 4001. This is below
  the cost-6 best recorded in the notes (§8.6). It is not a solution. It has not been checked with `EXDESC=1`, and
  its set is in the chain line of `runs/g4a.log`.
- **Cost 6**: g4b and g4c (two chains).

## Solutions

None. No `runs/g4?.txt` was written, no `cost 0` or `SOLVED` line appears in any log, and nothing was filed under
`research/frontier/sols/`.

## Context

The notes (§8.5, §8.7) estimate about 2.5e-4 per descent for a cost-0 state, about 4,000 descents or 55 CPU-hours.
This batch had 1865 descents, so the expected number of hits was about 0.47 (about a 37 % chance of at least one).
Zero hits is consistent with that estimate and does not change it much. The cost-3 state is one unit closer than
any earlier chain, which is some evidence the tail is not thinner than estimated.

## Notes on the run

- The `.out` files stay empty until a run ends (they hold the RESULT line only). The CHAIN lines, which carry the
  minima, are in the `.log` files. Both kinds are committed.
- Checkpoints (`runs/g4?.ckpt`) are not committed.
- The job was stopped at the six-hour mark with `pkill`. The `timeout 30000` in `launch.sh` would have run longer.
- The brief named the branch `claude/grind-10-8-4-<anything>`. The designated branch `claude/grind-10-8-4-5jv9d7`
  has 23 commits outside the research branch's history, so this work is on `claude/grind-10-8-4-runs`, based on
  `claude/bipartite-10-8-cell-um2c1t`. A draft PR was opened for it.
