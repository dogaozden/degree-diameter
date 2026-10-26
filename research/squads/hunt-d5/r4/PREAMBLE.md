# hunt-d5 squad, round 4: preamble (read ../r1/PREAMBLE.md for problem, machine rules, output format; ../r3/PREAMBLE.md for haar_fast)

Same rules: THREADS=1, every run `timeout <s> nice -n 10`, about 12 CPU-minutes, 35 minutes wall clock, no git, write
only in `research/squads/hunt-d5/r4/<card>/`, one JSON line to `research/squads/hunt-d5/r4/scoreboard.jsonl`.

## State after round 3 (all cost > 0 except where said)

- (9,5): Z53 ⋊₁₆ Z26 (order 1,378; n = 2,756) is the lead: **cost 2** twice (round 3 c2 seed 1016 with K=32 COOL=40;
  c3 seed 2035 with 12 s runs, K=8 COOL=6 REHEAT=30), cost 4 in ~20% of short seeds. Z197 ⋊ Z7 (1,379): 4.
- (7,5): (Z41 ⋊ Z5) × Z3 = Z41 ⋊₁₀ Z15 (615): **cost 2** (director, exact 3-swap move from a cost-4 set; no solution
  within 3 swaps of it); (Z61 ⋊ Z5) × Z2 (610), Z103 ⋊ Z6 (618): 4.
- (6,5) (new cell, published 684): **exact certificates: no Haar graph for C71 ⋊ C5 (355)**; (Z7 ⋊ Z3) × Z17 (357) and
  F₂₇ ⋊ C13 = SmallGroup(351,12): cost 4, and both are now certified exactly (no Haar graph); C3 × SL(2,5) =
  SmallGroup(360,51): cost 4 (open).
- (5,5): **exact: no Haar graph for any group of order 193–215 or 217–223** (positive control: the search finds the
  known order-176 solution). Order 216 and 224+ open.
- Route charts: 3-letter charts over F₃⁴ need a 4-cycle at every controller vertex; such controllers stop at m = 16.
  Per-edge F₂⁴ letters (tools/pelift, degree 6): cost 0 on controllers with 4-cycles (m = 12, 16, n = 384, 512),
  but on 4-cycle-free controllers a few fibres keep a diagonal gap (cost 32–48 at m = 12–14).

## Tools new this round (research/squads/hunt-d5/tools/)

- `haar_fast` now accepts env `SAVEBEST=1`: also writes `OUT.best<cost>` (same format) for near misses.
- `python3 metatab.py m k r T.bin` — table of Z_m ⋊_r Z_k in haar_fast's numbering (a·k + j), so a haar_fast near miss
  (n = 1 groups only) can be scored and improved with haar5: `python3 nm2idx.py OUT.best2` prints its indices.
- `haar5 lns T.bin d "S" r SECONDS SEED` — iterated exact large-neighbourhood search: tries every way of replacing r
  elements of S (identity kept), moves to the best (plateau moves allowed, no revisits). r = 2 is cheap at every Δ;
  r = 3 is ~10⁹ sets at Δ = 7 (minutes) and too slow at Δ = 9.
- `haar5 complete T.bin d "core" [LIMIT]` — every completion of a core set (exact for cost 0).
- `pelift CTRL SECONDS SEED [OUT]` (env DIAG=1 prints the failing controller pairs) — per-edge F₂⁴ route-chart lifts.
- `tables/` (shared, read-only for you): mt_53_26_16.bin, mt_41_15_10.bin, mt_61_10_9.bin, mt_103_6_56.bin,
  mt_197_7_104.bin (metatab tables), g351_12.bin, g357_1.bin, g360_51 (make it), and GAP tables.
- `haar_tab d 5 SECONDS SEED K OUT tab T.bin 1` — haar_fast on any GAP table (indices = table indices, so its near
  misses go straight into haar5); also takes SAVEBEST=1.
- Pipeline for near misses: farm with SAVEBEST=1 → `python3 ../../tools/nm2idx.py X.best2` (haar_fast, n = 1) or read
  the `tab(i)` indices (haar_tab) → `../../tools/haar5 lns T.bin d "<indices>" 2 120 1`.
