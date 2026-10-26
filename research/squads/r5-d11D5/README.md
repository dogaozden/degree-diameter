# Squad round r5-d11D5 (job resume4-cell-11-5, Oct 26 2026)

Goal: a doubled-matching (DM) base with **n = 587** points (W(8) plus two point-line pairs) and **structural cost 0**.
That is the step to (11,5) ≥ 7,044 (lift = 12n vertices; the current lab value is 7,032 = 12 · 586). Opus does the
later nu stage and the all-pairs check.

## The problem in one paragraph

A base is a 9-regular bipartite graph (n points, n lines) plus a bijection sigma: points -> lines. The file format
("plusopt format") is: first line `n 9`; then n lines, line l lists its 9 points; then n lines, sigma(0..n-1).
`SCORE=1 /tmp/po7 file.in` prints `cost=...` (number of failing (source, target, coset) triples, exact, 4 ms).
Cost 0 is the target. W(8) (n = 585) has cost 0 for every sigma. A "switch" adds one new point x* and one new line l*.

## What is new this round: sigma = delta o C

delta = the polarity of W(8); C = a collineation of PG(3,8) that is not a symplectic map. sigma(s) = delta(C(s)) makes
sigma^-1 of every pencil a PG-line, and every PG-line is a covering set of W(8), so one of the two coverage routes holds
everywhere. With it, all failures of a switched base are local to the switch.
- One switch, best design (`research/d11D5/dc/mkdc2.py`, an "incident regulus switch"): start cost 236-302
  (before: ~2,500). Its remaining failures are all coset +1 conditions from the new line l* and the switch lines L_i to
  other lines (line side).
- Two switches under one C (`mkdc2.py seed out.in 2`): start cost 604-1,310 by seed (e2_1 = 604, e2_10 = 606, e2_8 =
  624, e2_4 = 654). Files in research/d11D5/dc/.
- Plain annealing (po7, T0 2 -> 0.15) from e2_1 reaches ~100 in 500 CPU s, but it scrambles sigma (500+ points move
  away from delta o C). The old plateau without delta o C was 150-230.
- Annealing with sigma swaps restricted to ~250 points near the switches stalls at ~400; one switch alone stalls at ~100.
- `po7R` = po7 plus a penalty LAM per point whose sigma differs from a reference file (REF=...): keeps the structure.

## Tools (binaries are already built)

- `/tmp/po7` (research/d11D5/plus/plusopt7.c): annealer. env SECS (CPU s), SEED, T0, T1, PF (flag-move prob 0.3),
  PH (0.7), OUT (best state), OUT0 (written if cost 0 is reached), BLOCKS=file, SCORE=1 (score only).
- `/tmp/po7R` (research/d11D5/dc/po7R.c): po7 + REF=file (reference sigma) and LAM (penalty per deviating point),
  LOCAL=file (sigma swaps must involve a listed point). Prints dev = number of deviating points.
- `/tmp/wpo` (research/squads/r3-d11D5/c2/wpo.c): clause-weighting search; good from cost <= ~20, drifts up from 100+.
  env SECS, SEED, OUT, OUT0, LMAX (500), DECAY (50).
- research/d11D5/dc/: gq.py (W(8) coordinates: PTS, LINES, d_pt = polarity point->line, d_ln line->point, Bf the form,
  span, is_W, pmap, randmat, matinv), mkdc.py (9-flag regulus switch), mkdc2.py (incident regulus switch, KS=2 for two),
  dsig.py (replace sigma by delta o C), tagf.py + research/d11D5/inc/anal.py (failure classes:
  `python3 research/d11D5/inc/anal.py f.in 5000 > fails.txt; python3 research/d11D5/dc/tagf.py f.in fails.txt`),
  sdiff.py (how many sigma values / lines differ between two files), mkblk.py (local point set for BLOCKS).
  Run python from research/d11D5/dc (gq.py is imported from the current directory).
- Background notes: research/d11D5/NOTES.md (routes (a), (b), (c), demands, the earlier rounds), research/d11D5/dc/README.md.

## Machine rules (shared: ~4 cores, 15 GB, Opus runs 2-3 heavy jobs too)

- At most ONE heavy process of yours at a time, always `timeout 900 nice -n 10 ...`, THREADS=1, < 1.5 GB.
- Kill only your own processes, by PID (never `pkill -f`).
- No git commits. Write only in your card folder research/squads/r5-d11D5/<card>/.
- Time box: about 25 minutes in total.
- Scoreboard: append ONE JSON line to research/squads/r5-d11D5/scoreboard.jsonl:
  {"card": "cN", "idea": "<one line>", "code": "<path>", "command": "<exact>", "score": <lowest structural cost at
  n = 587 (or say n=586 in idea)>, "valid": <true if cost 0>, "best_file": "<path>", "next": "<one line>"}
  Then reply in at most 5 lines.
