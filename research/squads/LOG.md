# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-24, cell-12-8 (Opus, cloud session), round 1: (12,8), beat 4,650,100

Goal: a bipartite (12,8) graph above the table's 4,650,100 (Delorme 1985). Opus before the round: decoded the table
value as 2·35·|H(9)|, i.e. 7 × the (12,7) value 664,300 = Delorme's 5-level hexagon graph X_2 (same pattern at
Δ = 10, 11, 14, 16), so the target is a lift of "H(9) + 2 extra edges per vertex" by a group of order ≥ 36. Built
research/d12D8/tools (liftcheck scorer, nbwalks). Random voltages reach only order 12–14 at q = 9 (10 at q = 7, where
Delorme has 30); structured hop matchings raise the worst-case walk count from 6 to 25 but random second factors
still give ~1000 misses per source. Preamble: research/squads/d12D8_r1/CARD_COMMON.md.
Cards (squad A): c1 polychromatic point colourings as hop voltages · c2 apartment-holonomy voltages on H(9) alone
(far pairs) · c3 voltages from a 10-edge-colouring · c4 tripled-matching "bounce" designs · c5 sampled local search at
q = 9 · c7 non-abelian vs cyclic groups, random voltages · c8 literature (Delorme's construction) · c14 hard-target
analysis + rule. (squad B): c6 annealing calibration at q = 5 · c9 H(8) generator (q = 8, 3 hops, needs order 63) ·
c10 H(7) + 4 hops (needs order 119) · c11 route-chart lift feasibility at D = 8 · c12 dualities of H(9) (isometric
hops) · c13 GQ(11) incidence lifts (needs order 1589) · c15 wildcard · c16 star products (wildcard).
