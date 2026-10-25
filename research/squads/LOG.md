# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-25 14:20 UTC, job cell-11-5 (session_014q81WuY3QXemLJTaF8MiA2), goal (11,5) > 7,020, round r1-d11D5

Context: the cell was taken at 7,020 (W(8) + doubled matching over Z6, DM_D5.md) while this job was paused, so the
goal moved to > 7,020. Cards (scoreboard: r1-d11D5/scoreboard.jsonl):
- c1 algebraic Z3 cocycles on W(7) (cubic character of polynomial flag functions), for the tripled matching over Z9 (7,200): best 15,503, random level ≈ 16,000. Nothing.
- c2 group-invariant Z3 cocycles on W(7): no report at the time of writing.
- c3 σ-exemptions plus joint annealing of σ and ν on W(7): no report at the time of writing.
- c4 mixed chart lift over F3 (3 letters + 2 unit colours): valid only up to 2,916 (m = 18). At 7,128, 3.8% of pairs are far.
- c5 mixed chart lift over F4 (2 letters + 3 units) and F2: no diameter-5 lift at any m tried; 204k far pairs at 7,168.
- c6 Z4 lifts of the 1,782-vertex (11,4) graph: no report at the time of writing.
- c7 other W(q) + parallel-jump bases: exact walk-count bounds rule out W(5)+5/Z23, W(4)+6/Z42, W(3)+7/Z88. W(7)+2+1 over Z9 annealed to 82k far pairs (weak annealer).
- c8 augmentation of the 7,020 graph: every one of its 38,610 edges is critical (each deletion creates a distance-6 pair), and 20,000 twin-vertex attachments all failed.
Kept: nothing from the cards directly. c8's "every edge critical" pointed Opus to non-GQ bases for the
doubled-matching lift: W(8) plus one extra point-line pair (586 + 586), which would give 7,032 (see research/d11D5/NOTES.md).
Late r1 lines: c2 (invariant Z3 cocycles under tori/Singer/Sylow subgroups) best 8,356; c3 (σ-exemption + joint
annealing) 6,154; c6 proved that no lift of the 1,782 graph can work (568 vertices lie on no 4-cycle). Squad added
nothing directly. Opus's own lead (DM lift over W(8) + one extra pair) came from reading c8's "every edge is critical".

## 2026-10-25 17:05 UTC, job cell-11-5 (session_014q81WuY3QXemLJTaF8MiA2), goal: structural cost 0 for W(8)+1 (7,032), round r2-d11D5

Four cards only: the machine was CPU-bound by Opus's annealers. Each card got 1 process. Scoreboard: r2-d11D5/scoreboard.jsonl.
- c1 tabu search from the cost-2 state best_f5.in: never below 2; flag swaps cost +170 to +240 per move.
- c2 systematic move pairs on best_f5.in and best_g61.in: 185,814 first moves × 752,811 second moves, best stays 2.
- c3 multi-start over regulus-switch choices (15,731 starts over 4,160 hyperbolic lines): best start 68, annealed to 4.
- c4 exact σ-CSP with the base fixed: demand-only SAT is satisfiable but moves 585 points (cost 1,450); every
  demand-preserving change of up to 6 points (1,442 of them) costs ≥ 34; restricted annealing stays at 2.
Kept: the cost-2 states are deep local minima. Every independent route (Opus's annealers too) ends at one failing
demand pair (L_i, m ∋ p_i) or the fibre of x*/l*. The job stopped here (see research/squads/cells/d11D5.md).

## 2026-10-25 19:21 UTC, job resume3-cell-11-5 (session_018TRrddhVEdN311drmbPpBK), goal: structural cost 0 for an n > 585 DM base (W(8)+k), round r3-d11D5

Eight cards, one process each (the machine ran 7-9 heavy processes on 4 cores). Scoreboard: r3-d11D5/scoreboard.jsonl.
- c1 incident switch (x* on l*) with covering-set sigma (h hyperbolic line, regulus, transversal): 1,420 -> 6. Noted that a
  9-point dominating set of W(8) must be a PG-line (Bose-Burton), so both covering sets are forced to be lines.
- **c2 clause weighting (breakout) from the r2 cost-2 states: best_y901.in -> structural cost 0 at n = 586 in 325 CPU s**
  (r3-d11D5/c2/fail0_y901.in). The first cost-0 base for 7,032. SA, tabu, exhaustive move pairs (r2) never got below 2.
- c3 two-pair insertions (delta-based): no line by the time the round was cut.
- **c4 W(7)+1 test case (n = 401): 7-flag incident switch + the random-like sigma of the 4,800 record, plain SA (po7):
  structural cost 0.** Shows +1 works at all when sigma is not the polarity.
- c5 large neighbourhood destroy/repair: 2 (no change). c6 parallel tempering + crossover: 2 (no change).
- c7 Frobenius-equivariant 3-pair insertion: 966 (n = 588). c8 wildcard (sigma(x*) not l*, random bases): 1,506.
Kept: c2's weighting search and c4's random-sigma recipe. Opus runs the nu stage (inc/nujoint.c) on c2's base and on c4's
W(7)+1 base, and starts round r4 (more cost-0 bases, n = 587).
