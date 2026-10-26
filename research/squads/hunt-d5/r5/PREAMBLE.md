# hunt-d5 squad, round 5: preamble (read ../r1/PREAMBLE.md (rules, output) and ../r3/PREAMBLE.md (haar_fast) first)

Same rules: THREADS=1, every run `timeout <s> nice -n 10`, about 10 CPU-minutes, 35 minutes wall clock, no git, write
only in `research/squads/hunt-d5/r5/<card>/`, one JSON line to `research/squads/hunt-d5/r5/scoreboard.jsonl`.

## What produced the (9,5) record, and what to do now

The (9,5) graph on 2,756 vertices (Haar graph of Z53 ⋊₁₆ Z26) came from a **seed farm**: many short haar_fast runs
with `K = 16, COOL=10, REHEAT=40`, about 200 seeds; the winning seed hit cost 0 after 0.2 s. Solutions are isolated
(every single replacement in the solution costs 12–56), so exact neighbourhood searches from near misses do not reach
them; fresh seeds do. Rates seen: cost ≤ 2 in about 1–2 % of short seeds on the groups that later gave 0.

So this round is mostly farms on distinct groups, one script per card:
`../../tools/farm.sh DIR d SECONDS 16 SEED0 NSEEDS meta p k r n` with env `COOL=10 REHEAT=40` (it appends one
RESULT line per seed to DIR/farm.log and keeps near misses as DIR/s<seed>.sol.best<cost>; a cost-0 run writes
DIR/s<seed>.sol). Run it under `timeout <wall seconds> nice -n 10`. Pick SECONDS = 6 for Δ ≤ 7, 8 for Δ = 9.
**If a run reaches cost 0**: `python3 ../../../../frontier/build_haar2.py DIR/s<seed>.sol X.edges` must print VALID,
then `../../tools/apsp X.edges d 5`; report it in the first line of your reply.

Current best states: (7,5) Z41 ⋊₁₀ Z15 (615): cost 2 in 4 of ~230 director seeds; (Z61⋊Z5)×Z2 = meta 61 10 9 1
(610) and Z103 ⋊ Z6 = meta 103 6 56 1 (618): 4. (9,5) Z197 ⋊ Z7 = meta 197 7 104 1 (1,379): cost 2 in 2 of 26 seeds.
(6,5): best groups at cost 4 (SmallGroup(360,51) is being certified by the director; 355/1, 351/12, 357/1 have no
solution). (5,5): no Haar graph exists for orders 193–223 (exact).
