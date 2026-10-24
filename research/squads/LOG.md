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
- c1: annealing ν alone lowers Condition-A failures by a factor that shrinks with q: random/annealed = 7.0 (q=2),
  1.74 (q=3), 1.42 (q=4), 1.29 (q=5; 2.43 % vs 3.13 %).
- c2: quadratic-character formulas (bilinear, Plücker, quadratic-in-point, products) all converge to the random rate
  2⁻ᵠ (best 3.104 % vs 3.124 % at q=5). No algebraic advantage.
- c5: route coverage at q=4 can only be raised from 76.2 % to 77.9 % by annealing σ; distance-3 and distance-5 matchings do no
  better than random.
- c6: joint ν, σ annealing on GH(4): 20,985 → 10,901, still falling slowly.
- c3, c7, c8: no report at the time of writing.

Kept / what happened next (Opus): the hexagon case is closed (DM over GH(7) would need ν ~25× better than random on
the pairs without routes; nothing structured beats random). But the DM theorem holds for any generalized polygon,
and over generalized **quadrangles** (D = 5) the counting is favourable (≈ 10³ expected bad pairs vs q⁴ bits).
Joint annealing (dmfast NPOLY=4) solved W(7) and W(8) in minutes: **(10,5) 4,800** (table 4,000) and
**(11,5) 7,020** (table 5,850), both apsp VALID. Separately, the exp2-squad's hub trick (research/squads/exp2/hexd7 on
master) had never been run on H(8) because its generator needs odd q. hexgen2.c builds H(8), and one hub pair gives
**(10,7) 224,696** (table 224,694), apsp VALID. Did the squad help? Round 1 and 2 cards produced no record. Their
negative results (c1, c2, c4, c5) settled the hexagon question quickly, so the GQ idea came sooner. The wins
themselves are Opus solo work (DM theorem, reuse of the hub tool).

## 2026-10-24 22:38 UTC, cell-10-7 resumed (Opus, cloud session `claude/bipartite-10-7-uvpxk9`), round 3: more freed pairs

Goal: beat our (10,7) 224,718 (table 224,694). That graph is X(M) over H(8) plus 12 freed pairs, found by Opus
just before the round with a new **joint algebraic cover**: pairwise opposite freed flags, M maps each point to a line
with the same membership vector, then a growth mode adds pairs one at a time. Folder research/squads/d10D7-r3/
(README.md, cards.md, tools/hexkit.py, scoreboard.jsonl). Scorer: apsp.c on `d7hex edges`, or hexkit mismatch/uncovered.

Cards (best score):
c1 exact joint covers from structure: **max K with mismatch 0 = 4** (one zero quadruple in 10^5 samples; only ~5 % of
opposite triples are exact; H(2) flags no better) · c2 flag-set local search: mismatch 6,016 at K = 16 (random
6,000-7,300; about 1 % gain) · c3 leftover matching: no report · c4 q = 5 tuning (old binary): K = 19 then hub-graph
violations (cap q-1 = 4) · c5 q = 7 tuning: **K = 18 apsp VALID** (117,684; record 117,690 not beaten) · c6 proxy
(−,−)/(+,+) routes: no report (a K = 22 q = 5 solution left unverified) · c7 more than hubs: none valid (random-M
trials break diameter 7; hubs are 2 vertices per 3 deleted edges) · c8 new constructions: no report.

Kept / what happened next (Opus): the cards showed the joint algebraic cover cannot be exact beyond 4 flags in
H(8). In parallel Opus found two things the cards did not:
1. H(9) is self-dual. A duality M covers every absolute flag exactly, giving (11,7) 398,636 and, in the 5-level
   cover, (12,7) 664,412.
2. Watching the q = 9 growth add pairs with zero uncovered targets led to the **B2 condition**: M(B2(p)) = B2(l)
   alone covers a freed pair by type-2 routes. This gave (10,7) 224,828, (9,7) 117,760, (7,7) 23,500 and (11,7)
   404,222, all apsp VALID.
Did the squad help? Indirectly: the c1/c2 negatives closed the joint-cover line quickly, and c5's growth runs gave
the q = 7 calibration. The records came from Opus's own analysis.
