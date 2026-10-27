# grind-10-8-5: six-hour run of four orbit-search descents

Job: round 2 of the (10,8) cell grind (`research/squads/cells/d10D8.md` §8.7 and §9). Method and code unchanged from the cell branch (`claude/bipartite-10-8-cell-um2c1t`). Built `sym2/haar_sym2` with `gcc -O3 -march=native -fopenmp`; single-threaded per run.

## What ran

- Launch lines: `launch.sh g5a..g5d` with `RESTARTAFTER=0 COOL=15 REHEAT=30 ORBW=3`, groups `psl 23 97` (g5a, g5c) and `prod psl 7 sl 8 7` (g5b, g5d).
- Seeds 5001–5004 from about 23:19 UTC. The container restarted at about 00:45 UTC and killed all four runs. They were relaunched from their checkpoints on seeds 5005–5008 and resumed (`resumed from g5?.ckpt` lines in the logs).
- Stopped at about 05:19 UTC, six hours after launch. Each run's own clock reads 21,496 s.

## Results

| run | group | chains (descents) | lowest chain minimum (ORBW=3 energy) |
|---|---|---|---|
| g5a | psl 23 97 | 470 | 3 |
| g5b | prod psl 7 sl 8 7 | 461 | 6 |
| g5c | psl 23 97 | 464 | 9 |
| g5d | prod psl 7 sl 8 7 | 469 | 9 |

- Total descents: 1,864 (the `CHAIN` lines in the logs). Evaluations: about 169 million. CPU time: about 24 hours (four runs × 5.97 h).
- No solution: no `g5?.txt` file and no cost-0 line in any `.out`.
- Lowest value: 3 (g5a), the ORBW-weighted energy of a chain minimum, not a raw cost. Round 1's best was raw cost 6, so these numbers are not directly comparable.
- Consistency check: at the stated rate of about 2.5e-4 per descent, 1,864 descents give an expectation of about 0.47 solutions, so zero hits is well within chance. This round is about 44% of the 55 CPU-hour expectation, so it says little about whether the record is reachable. Combined with round 1 (about 7,400 descents), the total is about 9,300 descents with no solution.

## Files

- `research/d10D8/runs/g5a–g5d.log` (progress, `CHAIN` lines) and `.out` (RESULT lines): committed. Checkpoints (`.ckpt`) are not committed.
- No solution was found, so `verify.sh` was not run and nothing was filed under `research/frontier/sols/`.

## Operational notes

- The container restart killed the runs once; they resumed from checkpoints with new seeds, so the restart is not a method change, but it does mean the run mixes two seed sets.
- The git hook flagged uncommitted logs repeatedly, because the runs append to their logs continuously. Logs were committed on each hook fire and at the 30-minute cadence.
