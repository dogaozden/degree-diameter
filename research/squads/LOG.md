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
6,000-7,300; about 1 % gain) · c3 leftover matching (late report): greedy matching of leftover points to lines by
Hamming distance of membership vectors cuts uncovered targets at K = 21 from 66,296 to 22,967; swaps add 0.1 % · c4
q = 5 tuning: K = 19 apsp VALID (23,474), hub-graph violations at K = 20 · c5 q = 7 tuning: **K = 18 apsp VALID**
(117,684; record 117,690 not beaten) · c6 proxy (−,−)/(+,+) routes (late report): K = 22 at q = 5 apsp VALID (23,480),
which the old binary did not solve with the same settings · c7 more than hubs: none valid (random-M trials break
diameter 7; hubs are 2 vertices per 3 deleted edges) · c8 new constructions (late report): attaching a copy of H(2) to
X(M) over H(3) leaves 496 pairs at distance 8; no valid graph.

Kept / what happened next (Opus): the cards showed the joint algebraic cover cannot be exact beyond 4 flags in
H(8). In parallel Opus found two things the cards did not:
1. H(9) is self-dual. A duality M covers every absolute flag exactly, giving (11,7) 398,636 and, in the 5-level
   cover, (12,7) 664,412.
2. Watching the q = 9 growth add pairs with zero uncovered targets led to the **B2 condition**: M(B2(p)) = B2(l)
   alone covers a freed pair by type-2 routes. This gave (10,7) 224,828, (9,7) 117,760, (7,7) 23,500 and (11,7)
   404,222, all apsp VALID.
Did the squad help? Indirectly: the c1/c2 negatives closed the joint-cover line quickly, and c5's growth runs gave
the q = 7 calibration. The records came from Opus's own analysis.

## 2026-10-24 23:20 UTC, cell-10-7 (Opus, `claude/bipartite-10-7-uvpxk9`), round 4: bigger partial ovoids and spreads

Goal: after the B2 condition (research/d10D7/checks/B2_hubs_CHECK.md), the number of freed pairs at q = 5, 7, 8 is set
by two sizes: a set of pairwise opposite points (a partial ovoid) and a set of pairwise opposite lines (a partial
spread) of H(q). At q = 9 (duality) it is a set of pairwise non-collinear points. Greedy random gave 39/32 (q=5),
56/57 (q=7), 67/68 (q=8) and 2,821 (q=9). Folder research/squads/d10D7-r4/ (README.md, cards.md, tools/setcheck.c,
scoreboard.jsonl).

Cards (best scores, all checked by setcheck):
c1 H(8) points, k-fixed tabu: **134** (seeds gave 86, 134, 80, 102) · c2 H(8) points, algebra (torus orbits of
W(5,8) = F_{2^18}*/F_8*, exact max clique over orbits of order 19): 85 · c3 H(8) lines: **513 = q³+1**, the counting
maximum, from tabu on the orbits of an order-7 hexagon automorphism; the same pipeline on points gave 112 · c4 H(9)
non-collinear points, min-degree greedy + tabu: **3,911** · c5 H(7): **288 points, 344 lines** · c6 H(5): **72 points,
126 lines** · c7 "stars" (freed pairs at distance 4, centre w with M(w) = midline): K = 41 apsp VALID at q = 5, more than
the 32 of greedy opposite sets but less than c6's 72 · c8 wildcard: no gain; noted that one type-4 pair could join a B2
base (not built).

Kept / what happened next (Opus): the sets were plugged into `d7hex b2` / `b2dual` at once. (10,7) **224,962**
(K = 134 with a hyperplane spread of 513 lines; Opus built it from the elliptic section, and c3's search confirmed
513), (9,7) **118,224**, (7,7) **23,580** and (11,7) **406,402** were all apsp VALID. For the 5-level (12,7) graph Opus
replaced random hub graphs (diameter 8 at 5,642 hubs per side) by two copies of the incidence graph of H(5) joined by
two matchings, giving 7,812 hubs per side and **(12,7) 679,924**, apsp VALID. Did the squad help? Yes, directly: every
record of this round uses a set a card found.

## 2026-10-24 23:50 UTC, cell-10-7 round 5: larger partial ovoids of H(8)

Goal: points are the only bottleneck at q = 8 (513 lines exist), so each extra pairwise opposite point of H(8) adds 2
vertices to (10,7). Folder research/squads/d10D7-r5/ (README.md, cards.md, best134.txt, scoreboard.jsonl).

Cards: c1 ILS and exact closure LNS from the 134 set: no gain (every outside point conflicts with at least 3 set
points) · c2 more tabu seeds and settings: (see scoreboard) · c3 Hermitian field reduction (513 lines × 9 points
CSP): (see scoreboard) · c4 orbits of other subgroups as cores, then tabu: **217** (a 93-point core of 31 T_3-orbits,
then 170 s of k-fixed tabu) · c5 structure of the q = 7 set: the 288 set is one orbit of a stabiliser of order
1,451,520 = |Sp6(2)| inside the isometry group of Q(6,7), point stabiliser of order 5,040; no torus or Sp6(2) analogue at
q = 8; tabu inside an elliptic section Q⁻(5,8) gives 126 · c6 H(9) non-collinear: **4,277** = 47 orbits of an order-91
element of SL(3,9).

Kept / what happened next (Opus): verified both sets and rebuilt the graphs: **(10,7) 225,128** and **(11,7) 407,134**,
both apsp VALID. Opus noted that the 217 set has lost the T_3 symmetry (3 of 217 points map into the set), so the core
works as a basin, not a template. Opus also proved the upper bound 457 for partial ovoids of W(5,8), so there is room
left. Round 6 tests many structured starts. Did the squad help? Yes: both records come straight from cards c4 and c6.

## 2026-10-25 00:15 UTC, cell-10-7 round 6: structured starts, subgroup orbits, and the H(11) spin-offs

Goal: beat 217 pairwise opposite points of H(8) for (10,7), and raise the H(9) non-collinear set for (11,7). Folder
research/squads/d10D7-r6/ (README.md, cards.md, scoreboard.jsonl).

Opus finding at the start of the round: the 217 sets found independently by r5/c4 and r5/c3 are the same object. Each
is a union of two orbits of S7 × C3 ≤ Sp(6,2) × Gal(GF(8)/GF(2)): the 7 GF(2)-points of a maximal partial ovoid of a
W(5,2) subgeometry (Gram matrix J − I) plus one orbit of 210 points. This is also its full stabiliser. Exact searches
over unions of orbits give 217 again for S7, A7, S6, L3(2), 7:6, 7:3, S5×S2 and S4×S3, with or without the Frobenius
(research/d10D7/ovoid/orbsearch.py).

Cards:
- c1 many T_3 cores, then pov2: 217 only from r5/c4's core with seed 3. Other cores and seeds give 116–134, and
  33-orbit cores are worse.
- c2 groups outside Sp(6,2): the Singer 73:3 union (73) grows to 104 under pov2. SL(2,8) wr S3 and its subgroups, the
  diagonal SL(2,8) and Singer 511 give at most 9.
- c3 big kicks from 217: every kick (10–50 %, random, regional, crossover) regrows to the identical 217 set.
- c4 H(9): **4,291** = 613 orbits of the order-7 subgroup of the order-91 element. A k-fixed tabu on the 9,451-orbit
  graph was started from the 4,277 set.
- c5 H(5): no gain over 72. Unions of W(E7)-mod-5 orbits give at most 60.
- c6 H(9), orbit unions of SL(3,9) subgroups: A6 = Ω(3,9) gives 4,249 (exact), 91:3 4,186, L2(7) ≥ 3,913, SL(3,3)
  793, SU(3,3) 343. A tabu from the A6 union reaches 4,259.
- c7 H(11), structured: **756** pairwise opposite points. W(E7) mod 11 (7 reflections with Gram = E7 Cartan matrix) has
  7 orbits on the points of Q(6,11). Exactly one of them, of size 756, is pairwise opposite, and it is maximal. Unions
  over every reflection subsystem tried also cap at 756. Tabu from it found nothing more. Plain tabu gives 135.

Kept / what happened next (Opus):
- 217 looks like a hard local optimum for (10,7). The best union over every group tried is 217, and every outside point
  conflicts with at least 9 of its points. The upper bound stays 457.
- (12,7) **680,068**, apsp VALID: Opus replaced the doubled-H(5) hub graph with the 2-level cover of H(5) carrying the
  72 B2 hubs of the (7,7) solution. That gives 7,884 hubs per side, against the 7,812 of the doubled H(5).
- New spin-off cells over H(11), where the table values are 3-, 5- and 7-level hexagon covers. Opus built the Hermitian
  spread of 1,332 lines and a 135-point partial ovoid, using a new tabu (ovoid/potabu2.c) that computes conflicts on
  the fly. This gives (13,7) 1,063,206, (14,7) 1,772,100 and (15,7) 2,480,994; their checks are in
  research/d10D7/checks/hex11_B2_CHECK.md.
- (11,7) rebuilt with c4's 4,291 set.

Opus then ran c7's pipeline for other q. At q = 7 it gives exactly the 288 orbit. At q = 13 no W(E7)-orbit is
pairwise opposite, but unions over the E6 and A5 subsystems give 792 (greedy 131), which is used for (16,7).
Did the squad help? Yes, for (11,7) (c4) and for the negative evidence on 217 (c1, c2, c3), and decisively for the
H(11) spin-offs (c7's E7 construction, 5.6 times the tabu result). The spin-off cells and the S7 analysis came from Opus.
