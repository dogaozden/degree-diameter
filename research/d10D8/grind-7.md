# grind-7: fresh orbit-search descents for the (10,8) cell

Job: pure compute run, no method change. Four runs were planned (seeds 7001-7004). Two of them were lost to a container restart at about 01:07 UTC and replaced by seeds 7005-7008 under new tags. Branch: `claude/grind-10-8-7-fn6eh1-runs` (from `claude/bipartite-10-8-cell-um2c1t`).

## Runs

Launched with `launch.sh ... RESTARTAFTER=0 COOL=15 REHEAT=30 ORBW=3`. RESTARTAFTER=0 makes each stall start a fresh chain, so one CHAIN line = one fresh descent.

| tag | seed | group | descents | lowest chain cost |
|-----|------|-------|---------:|------------------:|
| g7a | 7001 | psl 23 97 | 144 | 6 |
| g7b | 7002 | prod psl 7 sl 8 7 | 140 | 12 |
| g7c | 7003 | psl 23 97 | 146 | 9 |
| g7d | 7004 | prod psl 7 sl 8 7 | 143 | 12 |
| g7e | 7005 | psl 23 97 | 311 | 6 |
| g7f | 7006 | prod psl 7 sl 8 7 | 321 | 6 |
| g7g | 7007 | psl 23 97 | 320 | 6 |
| g7h | 7008 | prod psl 7 sl 8 7 | 313 | 9 |

Total: 1,838 descents. g7a-d ran from 23:18 to about 01:07 UTC; g7e-h ran from 01:08 to about 05:10 UTC. Round 1 (grind-10-8-1..4) was about 7,400 descents with best cost 6, so the combined count is about 9,200.

## Result

No solution. No `runs/g7?.txt` file was written, and no "cost 0" or "SOLVED" marker appeared. Lowest cost seen: 6 (four runs reached it, none reached 0).

At the expected rate of about 2.5e-4 per descent, 1,838 descents give an expected count of about 0.46 solutions. A zero result is unsurprising, but it does not rule the cell out.

## Notes

- Checkpoints (`runs/*.ckpt`) and raw logs (`runs/*.log`, `runs/*.out`) stay local; they are excluded through `.git/info/exclude`.
- Text tails are committed as `runs/g7?.tail.txt`.
- All runs were stopped at about 05:10 UTC, at the end of the 6-hour window.
