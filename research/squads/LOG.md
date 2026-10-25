# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-24 ~18:20 UTC, session thm-d8table (claude/d8-numerology-ocg3xq), round r1-d8

Goal: a structured lift of the hexagon H(q) plus two extra point-line matchings with many copies and diameter 8
(explain/beat the Delorme–Gómez–Quisquater D = 8 cells). Test bed q = 5: random lifts reach M ~ 12, DGQ's formula
gives 25, M >= 27 would beat (8,8). Scorer: research/theorems/d8/liftdiam (exact BFS over all sources).
Cards (research/squads/r1-d8/cards.md):
- c1 hyperplane-pencil labels on hops: best M=10 with 16 unreached; worse than random labels. Found a real bug in
  liftdiam (disconnected lifts reported as 0 unreached); fixed in the shared file, all zeros rechecked.
- c2 square-class/quadratic holonomy on flags: M=10 ok, M=15 178 unreached (random 192); lowers geodesic variety.
- c3 annealing of Z_k labels (Z_5 polygon part fixed): no M above random (full counts 76,002 unreached at M = 20 and
  478,608 at M = 25, random starts about 78k and 500k; a 64-source sample was overfit).
- c4 torus-invariant labels: no T-equivariant hop matching exists at q = 5 (stabilizer types differ on points and
  lines); with the 2-torsion K4 instead, sampled 11,628 unreached at M = 20 and 79,476 at M = 25. No M above random.
- c5 colour-class voltages in a cyclic group: best 2 unreached at M=14 (best of the round; random ~12).
- c6 j=1 designs: only the M=4 baseline verified; M=5 annealing left 1566 unreached.
- c7 apartment-projection labels: worse than random (potential-type labels collapse one-hop walks).
- c8 non-abelian/permutation voltages (own checker gperm, agrees with liftdiam): no gain over abelian.
Kept: c5's colour voltages (closest), c7's lesson (labels must be locally injective), c1's bug fix.
Next: nothing in the round approached 25 at q=5; I wrote up the analysis (research/theorems/D8_NUMEROLOGY.md) and
continued with annealing on the exact diameter for j=1 at q=3,4 myself. Honest verdict: the squad added breadth and
a bug fix, no construction.


## 2026-10-24 ~19:30 UTC, session thm-d8table (claude/d8-numerology-ocg3xq), round r2-d8

Goal as in r1-d8, plus the "V + E" lead: for odd q DGQ's D = 8 value is |V(X)| + |E(X)| for X their diameter-7
Z_5 polygon cover. Cards (research/squads/r2-d8/cards.md), scored by liftdiam (exact unreached pairs at D = 8):
- d1 V + E operation on small polygon covers: H(3) cover X (3,640 vertices, degree 6, diameter 7) -> Y on |V| + |E|
  = 14,560 vertices, degree 6, bipartite: diameter 9 (126 unreached at D = 8 with local sigma, 164 for a random
  6-regular bipartite graph of the same order). Random level.
- d2 "two copies + out-arcs" bases with a Z_5 lift at q = 3: best 379,152 unreached at M = 5; annealing gains 4%.
- d3 colour voltages with the Z_5 part (evolving r1/c5) at q = 5: M = 15 not closed (best exact 188 unreached).
- d4 targeted annealing, one matching, q = 4, M = 8 = q + 4: best 598 unreached (random start 3,912), still falling
  when its time ran out; I resumed it myself for 30 minutes (D8_NUMEROLOGY.md §2.2).
- d5 anti-homomorphic hop matching at q = 3: no exact one (annealing plateaus at about 4,550 violations of 21,840);
  lifts built on it reach M = 20 for 2 of 300 label seeds, the same as random matchings.
- d6 literature: NOT FOUND. No accessible bibliography cites the DGQ paper; no diameter-8 hexagon construction and
  no "diameter + 1, degree kept, order x (1 + Δ/2)" operation in the record (wiki itself unreachable: HTTP 503 /
  TLS, not bypassed). Nearest unread item: Bond and Delorme, Ars Combin. 25-C (1988). Notes: r2-d8/d6/notes.md.
- d7 wildcard, duality hops at q = 3: 16 copies against 17 for random; two dualities worse.
- d8 GF(q)*/{±1} frame labels for the (13,8) cell, Z_3 x Z_3 at q = 7: sampled 177,630 unreached against 170,535 for
  random labels.
Kept: nothing new; d4's state was the only one still improving. Honest verdict: two rounds, 16 strategies, no
structured idea beat random lifts, and the targeted annealer is the only tool that moved the count much.

## 2026-10-25 ~09:55 UTC, session thm-d8table resumed (claude/d8-table-numerology-mi6but), round r3-d8

Goal: structured lifts of H(q) + 2 hop matchings with diameter 8 and many copies (explain or beat the DGQ D = 8
cells; DGQ's formula gives 20, 20, 25 copies at q = 3, 4, 5). Scorer liftdiam (exact), valid files rechecked with apsp.c.
Cards (research/squads/r3-d8/cards.md):
- c1 near-duality hop matchings (annealed so collinear points go to concurrent lines): no gain over random matchings
  in the lift tests at q = 5 (M = 12 both; M = 14 fails for both).
- c2 flag voltages designed for many distinct geodesic voltages, Z_5 polygon cover x Z_K with random hop labels: K = 3
  fails at q = 4, 5 (designed 192 vs random 196 unreached at q = 5).
- c3 exact-cost annealing at q = 4: M = 20 valid (DGQ's value); M = 21 at 36 unreached.
- c4 the same at q = 5: M = 14 valid; M = 16 at 6.
- c5 statistics of optimized lifts vs random: largest |z| 3.6 (hop-2 labels slightly more often distinct around a point).
- c6 duality hops at q = 3 with annealed labels: M = 22 valid with one duality + one random matching; two dualities worst.
- c7 SAT (pysat) for guaranteed-walk label designs: only tiny cases (q = 2, j = 2, M <= 7).
- c8 wildcard, C_7-equivariant lift at q = 4 (Singer element of SL(3,4)): M = 16 with random voltages.
Kept: c8's equivariant lifts (generalized to eqlift.py with any semiregular cyclic collineation group, plus a quotient
annealer qanneal2.c): q = 4 M = 22 and q = 5 M = 20 valid; c6/c3/c4 as calibration (DGQ's formula is passed by
optimization at q = 3, 4). Following c2, annealing the polygon cover x Z_K myself gave K = 5 at q = 3 (25 copies).
Verdict: the squad gave calibration data and one useful tool (c8); no structure behind DGQ's numbers.
