# Squad round r6-d11D5 (job resume4-cell-11-5, Oct 26 2026)

Goal: a doubled-matching (DM) base with **n = 588** points (W(8) plus THREE point-line pairs) and **structural cost 0**,
the step to (11,5) ≥ 7,056. (n = 589, four pairs, is a bonus.) Opus does the nu stage and the all-pairs check.

## Where we are

Read research/squads/r5-d11D5/README.md first (file format, cost, sigma = delta o C, tools, machine rules); it all
still holds. Since then:
- **n = 587 is solved** (7,044, research/d11D5/graphs/d11D5_n7044_CHECK.md) by the **K22 switch** (round r5 card c8):
  new points x*, y* BOTH on new lines l*, m*; x* on 7 old lines delta(R) for R on a hyperbolic line h1, y* on 7 from
  h2; the 14 removed points split 7/7 onto l*, m*; sigma = delta o C, with sigma(C^-1(Ra)) = l*, sigma(x*) =
  delta(Ra) for a spare point Ra of h1 (same for y*). Pipeline: start 414 -> po7 (T0 2 -> 0.15, 400 s) 18 -> cold po7
  (T0 0.6 -> 0.08) 12 -> /tmp/wpo with LMAX=3000 DECAY=10 -> 0. wpo only works from cost <= ~20.
- A general builder: `research/d11D5/dc/kkk.py KK seed out.in tries` (run with PYTHONPATH=research/d11D5/dc or from
  that folder). env PAT="i-j,i-j,..." gives any incidence pattern between new point i and new line j (K new points
  and K new lines; each new point gets 9 - (its new lines) old lines from its own hyperbolic line, each new line gets
  9 - (its new points) moved points); K=3 (no PAT) is the complete block K33; CYC=1 a cycle; PLANE=1 puts all
  hyperbolic lines through one point R0 of the plane where C keeps every switch line isotropic.
  Examples: `PAT="0-0,0-1,1-0,1-1" python3 kkk.py 1 9 out.in 5` (K22, ~446); `K=3 python3 kkk.py 1 1 out.in 8` (K33).
- `/tmp/po7R` has a GREEDY mode: `GREEDY=585 OUT=g.in /tmp/po7R start.in` does steepest descent over sigma swaps at
  the new vertices (ids >= 585) and their sigma partners; it takes ~100 off a start.
- **n = 588 so far:** K33 starts 622-776 (greedy-polished); po7 900 s from them: 214-292; long 1,800 s anneals
  running (Opus). Cycle C6 starts 924+; K33 with PLANE=1 952+. n = 589: two K22 blocks 1,146 (anneal stuck at
  ~520-790), K44 1,240, C8 1,374. The step from 2 to 3 pairs is much harder than the start costs suggest: K33
  anneals stall at ~200 with failures spread into the bulk, while K22 went 414 -> 18.

## Machine rules
As in r5 (one heavy process at a time, `timeout 900 nice -n 10`, THREADS=1, < 1.5 GB, kill only your own PIDs, no
git, write only in research/squads/r6-d11D5/<card>/). Opus runs 2 long anneals. Time box about 30 minutes.

## Scoreboard
Append ONE JSON line to research/squads/r6-d11D5/scoreboard.jsonl:
{"card": "cN", "idea": "<one line>", "code": "<path>", "command": "<exact>", "start": <best start cost>,
 "score": <lowest structural cost reached after annealing, at n = 588 (or say n in the idea)>, "valid": <cost 0?>,
 "best_file": "<path>", "next": "<one line>"}. Then reply in at most 5 lines.
