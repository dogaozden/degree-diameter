# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-24 18:40 UTC, cell-10-7 (Opus, cloud session `claude/cell-10-7-search-l1bqxx`), round 1: a 4th sheet over GH(q)

Goal: beat (10,7) = 224,694 = 3·|GH(8)| (the polygon cover: GH(8) + one matching, Z₃ voltages; rebuilt and checked
here). A 4th sheet over GH(8) + 1 matching would give 299,592. Shared testbed: GH(3) + 1 matching, group of order 4
(2,912 vertices, Δ = 5), scorer `research/d10D7/lift2` (exact lift diameter cost). Counting predicted failure for
random-like voltages (≈ 4.3k nats of freedom vs ≈ 22k expected misses). Folder research/squads/d10D7-r1/.

Cards (best full cost; random start ≈ 22k; 0 = solved): c1 free annealing Z₄ 6,171 · c2 Z₂×Z₂ (no report line) ·
c3 zero hexagon voltages + free matching voltages 4,700 · c4 constant matching voltage + structured hexagon
voltages (no report line) · c5 doubled flags (σ a 1-factor of the hexagon) **3,332** · c6 matching chosen by NB-walk
counts 6,599 (walk counts are not the bottleneck: min 6 achieved) · c7 walk-repair moves 6,325 (ties plain
annealing) · c8 S₄ permutation (non-regular) covers ≈ 8,400 in lift2 units.

Kept: nothing solved, as predicted. The DIAG breakdown (misses only at even hexagon distance 0, 2, 4, 6) and c5's
"doubled flags help close pairs" led Opus to the doubled-matching construction (DM, research/squads/cells/d10D7.md
§4), which removes every miss except sheets {0,3} of opposite pairs.

## 2026-10-24 19:03 UTC, cell-10-7 round 2: the doubled-matching (DM) sub-problem

DM: GH(7) + one doubled matching over Z₆ would give 235,296 > 224,694 if every opposite pair has either geodesics
of both ν-parities (Condition A) or a route. Folder research/squads/d10D7-r2/ (README states the problem).
Cards: c1 annealing floor of Condition A at q = 4, 5 · c2 quadratic-character formulas in point/line coordinates ·
c3 coordinate (Plücker) formulas · c4 relative-position voltages (distances to reference vertices) · c5 matchings
with maximal route coverage · c6 joint annealing at q = 4 · c7 exact SAT/MaxSAT for Condition A at q = 2 · c8 wildcard.
Outcomes (filled in as the cards report):
- c4: relative-position voltages are worse than random flag-level ν (q = 5: 11.8 % failures vs 3.1 %; q = 3: 13.7 %
  vs 12.4 %). Coarse partitions correlate the parities of the q+1 geodesics.
