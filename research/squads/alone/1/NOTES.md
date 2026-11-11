# Squad alone-1 notes: Haar graphs of SL(2,q) x Z_n and PSL(2,q) x Z_n, degree 16, diameter 5

Target: more than 31,460 vertices (N = |G| > 15,730 per side). Tool: `haar_gen3` (research/frontier), 1 thread per run.

## Result

No graph beating the target. Best verified result: a degree-16, diameter-5 Haar graph on SL(2,11) x Z_6 (N = 7,920, 15,840 vertices), checked by build_haar2.py (VALID) and by the tool's own full diameter check. The 5,280-per-side graph on SL(2,11) x Z_4 (10,560 vertices) is also verified.

## What was run

1. Sanity check, D = 5, d = 9 on SL(2,11) (a known record, 2,640 vertices): 2 uncovered after 90 s. Not solved in this budget, so the tool is somewhat weaker than the earlier agent's search on that case.
2. Degree-16 probes on SL(2,11) x Z_n (90 s each, unless noted):
   - n = 4 (N = 5,280): solved, verified.
   - n = 6 (N = 7,920): solved, verified.
   - n = 8 (N = 10,560): best 14 uncovered.
   - n = 10 (N = 13,200): best 152 uncovered.
   - n = 12 (N = 15,840), 60 s: best 528 uncovered.
3. Sweep of 12 groups with order just above 15,730, 240 s each, 4 in parallel:

| group | order N | best uncovered |
|---|---|---|
| SL(2,7) x Z_47 | 15,792 | 518 |
| SL(2,11) x Z_12 | 15,840 | 484 |
| PSL(2,11) x Z_24 | 15,840 | 526 |
| SL(2,5) x Z_132 | 15,840 | 576 |
| SL(2,9) x Z_22 | 15,840 | 502 |
| PSL(2,9) x Z_44 | 15,840 | 545 |
| PSL(2,8) x Z_32 | 16,128 | 602 |
| PSL(2,13) x Z_15 | 16,380 | 615 |
| PSL(2,16) x Z_4 | 16,320 | 717 |
| PSL(2,19) x Z_5 | 17,100 | 793 |
| PSL(2,17) x Z_7 | 17,136 | 822 |
| SL(2,13) x Z_8 | 17,472 | 878 |

## Reading

- Every group at order about 15.8K sits at roughly 480–600 uncovered elements after 240 s, about 3–4% of the group. None is near zero, and the larger orders are worse. The per-element coverage is random-like, and annealing from random S only reduces it slowly.
- The wall for degree 16 on SL(2,11) is between N = 7,920 (solved in seconds) and N = 10,560 (14 left after 90 s). The 15,730-per-side target is about 2× past that wall.
- Nothing in this region reached the target, so no record claim is made. The residuals are too far from zero for a longer run on the same groups to be the next step without a better search method.

## Ideas not tried (next steps)

- Longer runs (hours) on SL(2,11) x Z_8 or Z_10, to measure the wall more precisely.
- Symmetric S (orbit search, research/structured/haar_sym.c, on branch claude/structured-search-orbit-w5dd4f).
- Groups with a richer structure than SL/PSL x cyclic, which the other squad regions cover.

Scoreboard: scoreboard.jsonl (one line per attempt; score = vertex count if valid, uncovered count otherwise).
