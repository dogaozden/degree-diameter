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

## 2026-10-25 19:52 UTC, job resume3-cell-11-5 (session_018TRrddhVEdN311drmbPpBK), goal: more cost-0 bases and n = 587, round r4-d11D5

Four cards (r4-d11D5/scoreboard.jsonl). Meanwhile Opus finished the nu stage on r3 c2's base: **(11,5) 7,032, apsp VALID**
(research/d11D5/graphs/d11D5_n7032_CHECK.md).
- c1 wpo from the other r2 cost-2/4 states: 7 more cost-0 bases at n = 586 (f5, g61, u602, d1s13, h71, h72, m81), each in
  1-3 minutes. Stopped once 7,032 was verified.
- c2 n = 587 on top of fail0_y901 (second switch, SA, then wpo): SA 1,904 -> 214; wpo from 214 drifted up to 626; longer
  SA (T0 3-8, 600 s) stays at 214-218.
- c3 random-sigma incident switch on W(8) (r3 c4's recipe): SA 1,828 -> 4 in 400 s; stopped (n = 586 already solved).
- c4 two insertions at once into W(8) with the 7,020 sigma (genk.py k = 2, start 3,814): SA 392, colder SA 164, no further gain.
Kept: wpo only from low cost (<= ~20); SA first. Opus's own n = 587 runs (a pair added to the solved 7,032 base, 9- and
8-flag switches, T0 3-20, 91 points near the first pair frozen, wpo with LMAX 4000) all plateau at 150-230, while a
single pair added to W(8) with the same SA reaches 12 (and r4 c3 reached 4). A second pair interferes with the first
through sigma globally (every sigma(s) is on the coverage routes of every new vertex), so n = 587 needs a better
structural search than SA + wpo. The squad added the decisive tool (wpo) in r3; in r4 it added nothing new.
After r4 (Opus alone): the one-pair pipeline (inc/pipeline.sh: po7, wpo, nujoint TARGET, finish.sh) gave the side
results (10,5) 4,812 (W(7)+1) and (12,5) 9,852 (W(9)+1) in about 10 minutes each, both apsp VALID. A control showed that
one pair added to W(8) with the 7,020 sigma anneals to 10 and wpo finishes it in 39 s, while a second pair on any
solved n = 586 base stays at 150-400.


## 2026-10-25 23:40 UTC, job resume4-cell-11-5 (session_01YVUXzZUE2Fjy42D4zug9Gh), goal: structural cost 0 at n = 587 (11,5 ≥ 7,044), round r5-d11D5

Opus first found a structured sigma, sigma = delta o C (the polarity of W(8) after a non-symplectic collineation C of
PG(3,8)): it makes sigma^-1 of every pencil a PG-line, hence a covering set, so all failures of a switched base are
local to the switch (research/d11D5/dc/README.md). Two-pair starts dropped from 2,000-5,000 to ~600 (mkdc2.py KS=2).
Eight cards around that (r5-d11D5/README.md, scoreboard.jsonl; best structural cost at n = 587):
- c1 plain pipeline on 18 more mkdc2 KS=2 starts: 600 -> 76 (one anneal; no time for wpo).
- c2 penalised annealer po7R (REF sigma, LAM per deviating point): 68 (LAM 1 then 0.2); LAM 2 keeps the structure
  (dev 199) but stalls at 144. The penalty trades structure for cost; it does not give both.
- c3 wpoR (wpo + reference penalty + weight cap) written; only its po7R pre-anneal ran: 98.
- c4 9-flag regulus pairs and 9-flag + incident pairs under one C: best start 588, annealed 106; not better than mkdc2.
- c5 the moved points on a hyperbolic line g (the new LINE structured): one pair 196, two pairs 414 -> 176; failures
  move from the line side to the point side.
- c6 local search over the free choices of the start (C, p_i, omitted points, sigma partner of x*): 584 -> 306; only
  the sigma partner of x* and the p_i moves were ever accepted.
- c7 targeted tabu steepest descent: 604 -> 226 with only 95 sigma values changed (still falling when stopped).
- **c8 wildcard: the K22 switch** (x*, y* both on two new lines l*, m*, each on 7 old lines delta(R) of a hyperbolic
  line; sigma = delta o C): start 414, anneal **18**.
Opus kept c8's design: cold anneal 18 -> 12 (two seeds, same 6 conditions), wpo with LMAX 3000 DECAY 10 (the default
LMAX 500 drifts up from 12-18) -> 8 -> 2 (one coset-0 demand: a switch line and an old line through its moved point)
-> 0, nujoint TARGET=1 from a random nu -> 0 violated in 89 s, finish.sh: **(11,5) 7,044, apsp VALID**, independent
numpy BFS agrees (research/d11D5/graphs/d11D5_n7044_CHECK.md). Opus's own two-pair runs from mkdc2 starts reached 52.
The squad's wildcard made the decisive design; Opus's delta o C made the starts low enough for it.

## 2026-10-26 01:23 UTC, job resume4-cell-11-5 (session_01YVUXzZUE2Fjy42D4zug9Gh), goal: structural cost 0 at n = 588 (three pairs, 11,5 ≥ 7,056), round r6-d11D5

Eight cards (r6-d11D5/README.md, scoreboard.jsonl; machine load ~10 on 4 cores, so most anneals were cut early).
Best structural cost at n = 588 (start -> annealed):
- c1 survey of the 17 incidence patterns of 3 new points x 3 new lines (kkk.py PAT): starts 682 (path P6) to 1,092;
  K33 842, C6 830; anneals 398 (P6), 412 (theta). Start costs differ by less than their spread over seeds.
- c2 4+4 patterns (n = 589): cube Q3 1,180, K44 1,196, two K22 1,298, C8 1,334; Q3 annealed to 850.
- c3 K33 schedule (T0 0.5 -> 0.05, 400 s): 392.
- c4 wider greedy polish (moved points, switch-line points and their sigma partners): K33 648 -> 476, anneal 294.
- c5 geometry chosen for the coset-0 demands: for random C no hyperbolic line has more than 2 points of S, so at most
  6 of 18 K33 switch lines stay isotropic; start 708, anneal 294.
- c6 a third pair attached to the solved 7,044 base: start 1,594 (428 hot points: the annealed sigma has no slack
  left), anneal 532.
- c7 K32 block, block-internal sigma, two hyperbolic lines per new point: 942 -> 474; all worse than kkk.py.
- **c8 analysis + C6 in the plane**: K22 keeps all 14 switch lines isotropic (S is a plane and both hyperbolic lines
  lie in it), K33 6 of 18; K22 new points miss 102-114 vertices, K33 151-159. Built the 6-cycle block with all
  three hyperbolic lines through one point of the plane (kkk.py PLANE=1 PAT C6, 21/21 isotropic): start 622, anneal
  **152** (still falling when cut).
Opus kept c8's start: cold anneals 152 -> 70 -> 60 (research/d11D5/dc/n588_c6plane_cost70.in); wpo (LMAX 3000-6000)
from 60-70 only reaches 68 and drifts. Fresh C6-plane starts (624-874) anneal to 142-178; Opus's own triangle design
(tri.py: every new point's pencil preimage a full PG-line) 638 -> 120; long K33 anneals 148-168.
The squad again supplied the best design (c8); n = 588 stayed open at 60.
