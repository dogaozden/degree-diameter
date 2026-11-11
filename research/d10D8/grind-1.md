# d10D8 grind-1: six-hour run of four orbit-search runs (no solution)

Branch: `claude/grind-10-8-1-d10d8` (from `claude/bipartite-10-8-cell-um2c1t`). Run 2026-10-26, 17:00 to 23:00 UTC.

## What ran

- Method unchanged: `sym2/haar_sym2` built from `sym2/haar_sym2.c` with `gcc -O3 -march=native -o sym2/haar_sym2 sym2/haar_sym2.c -lm`, no code changes.
- Four runs, one per core, via `launch.sh`, all with `ORBIT="3 3 1" RESTARTAFTER=0 COOL=15 REHEAT=30 ORBW=3`, `10 8 28000`:

| tag | seed | group | chains | lowest chain minimum | evals |
|---|---|---|---|---|---|
| g1a | 1001 | psl 23 97 | 465 | 9 | 41.8M |
| g1b | 1002 | prod psl 7 sl 8 7 | 474 | 12 | 36.5M |
| g1c | 1003 | psl 23 97 | 473 | **6** | 41.7M |
| g1d | 1004 | prod psl 7 sl 8 7 | 470 | 9 | 36.8M |

Total: **1,882 fresh descents** (chains), about 157M evaluations, about 24 CPU-hours.

## Lowest costs seen

- Lowest chain minimum: **6**, once (g1c, chain 193, seed 1003; `S 24541 424109 100203 528429 78813 561793 296414 426331 372361 220196`).
- Chain minima over all 1,882 descents: cost 6: 1, cost 9: 14, cost 12: 62, cost 15: 235, cost 18: 509, cost 21: 666, cost 24: 356, cost 27: 39.

## Result

No cost-0 descent. No `g1?.txt` solution file was written and no `cost 0` / `SOLVED` line appeared in any log. No verification was needed, so `verify.sh` was not run and nothing was filed under `research/frontier/sols/`.

For scale: at the stated per-descent probability of about 2.5e-4, 1,882 descents give an expected 0.47 hits, so a miss is not surprising (about a 37% chance of at least one hit at that rate). This run does not change the estimate.

## Notes

- The runs were stopped with `pkill` at 23:00 UTC. The `.ckpt` checkpoints are left untracked and uncommitted, as the job requires; they hold the best sets for resumption.
- The `.out` files stayed empty because the RESULT line is only written on exit. The `CHAIN` statistics are in the `.log` files, which are what was committed as tails.
