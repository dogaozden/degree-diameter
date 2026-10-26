# Audit of the bipartite degree–diameter table (Δ = 3..16, D = 3..10)

Project `table-audit`, Opus lead, 2026-10-25. Brief: rebuild every entry we can, find who holds each value and the
construction, check the graph, and flag entries that do not check out or have no traceable construction.

- Per-cell results: [`cells.md`](cells.md) (table) and [`cells.csv`](cells.csv) (all fields: value, 2013 survey value,
  holder, source, construction, rebuilt, check, upper bound, Moore bound, our record, flag, notes).
- Literature notes (sources read, what is primary and what is inferred): [`lit/LITERATURE.md`](lit/LITERATURE.md).
- Checks: [`checks/`](checks/), commands in [`checks/CHECKS.md`](checks/CHECKS.md). Builders: [`tools/`](tools/).

Status and open items: [`HANDOFF.md`](HANDOFF.md).

## 1. Which table

The live Combinatorics Wiki page (http://combinatoricswiki.org/wiki/The_Degree_Diameter_Problem_for_Bipartite_Graphs,
oldid 649, last edited 18 Feb 2022) is readable over plain http (https fails TLS from this container; I did not bypass
TLS). I parsed its values, cell colours (the wiki's holder key) and its upper-bound table into
[`lit/wiki_table_2026-10-25.json`](lit/wiki_table_2026-10-25.json). It is the table this audit checks.

- It equals the 2013 survey table (Miller–Širáň DS14v2, Table 4) except (13,3) 270 → 274 and (15,3) 370 → 374
  (Araujo-Pardo–López, edited 30 Mar 2021). The page history has no other value change since 17 Jan 2012.
- **(11,10) = 130,592,354.** The survey's "130 592 1354" is a typo; every wiki revision has 130,592,354.
- Holder counts by colour: Moore 27, Loz 39, Delorme–Gómez–Quisquater 27, Delorme–Farhi 11, Hafner/Loz 3,
  Araujo-Pardo–López 2, Feria-Purón–Miller–Pineda-Villavicencio/AL 1, Bar-Yehuda–Etzion/Bond–Delorme 1,
  Conder–Nedela/DGQ/Loz 1.

## 2. Summary

<!-- SUMMARY -->
Of the 112 cells (counts from cells.csv):

- **47 rebuilt** with the holder's own construction, or from the holder's own graph file, at exactly the table value and
  checked valid: the 27 Moore cells, (3,5), (7,3), (3,7), (4,5), (4,7), the Delorme–Farhi cells at D = 4 and 6 (10),
  the three D = 3 AL/FMP cells, and (6,7), (8,7) (Delorme 1985 §9).
- **54 reproduced at exactly the table order** by a construction of the same family or a graph found here, when the
  holder's own description is missing: the 15 green D = 5 and D = 7 cells (polygon covers), (3,8) and (3,10) (cyclic
  lifts found by the squad and the lead), (16,3) (a Delorme–Farhi duplication on PG(2,13)), (13,8) (round 2: a Haar graph
  of PSL(2,37) × Z105; the DGQ construction itself is not known), and 35 Loz cells as Haar graphs of
  metacyclic groups (§3).
- **6 INVALID as read**: (10,8), (11,8), (12,8), (14,8), (15,8), (16,8). Their values are Gómez's ΩH_q (PhD thesis,
  Barcelona 1986, §2.9.3), but that construction, as drawn, has diameter 9, not 8 (§4; witness pair for (10,8) in
  checks/witness_omega_thesis.txt). Relabelling the copies freely fixes it at q = 2 and 3 but no such labelling is known
  at the table's q = 7..13 (§7).
- **5 have no traceable construction**: 4 Loz cells (data lost: (13,10), (14,10), (15,10), (16,10)),
  and (16,5).
<!-- /SUMMARY -->

No table value was found to be wrong outright: every cell with a construction I could rebuild checks out, and no value
exceeds its upper bound. The doubtful ones are the six D = 8 cells above. Four of them, (10,8), (12,8), (14,8),
(16,8), are also cells the repo has not beaten, so the table value is the only claim there.

## 3. What was rebuilt, family by family

Every rebuilt graph was written as an edge list and checked by `research/lifts/coordinator_check/apsp.c` (all-pairs,
no symmetry), by `apsp_mt.c` (the same with threads), or, for the level covers, by `apsp_orb.c` (BFS from one level
plus a check, edge by edge, that the level shift is an automorphism). The only exception is the three Haar graphs above
10⁶ vertices (§3, Loz), checked by two independent two-BFS Haar checkers. The builders are mine (tools/), except the
Araujo-Pardo–López graph (problems/bipartite_dd/lib.py) and the Haar rebuild (research/frontier/build_haar2.py).

**Bipartite Moore graphs (27 cells, optimal).** Incidence graphs of PG(2,q) (D = 3), the generalized quadrangle W(q)
(D = 4) and the split Cayley hexagon H(q) (D = 6) for q = 2, 3, 4, 5, 7, 8, 9, 11, 13, built by
`tools/moore_build.c` (any prime power q ≤ 16, including even q, which research/p4/d6/hexgen.c does not cover; H(q)
from Tits' coordinates, with counts checked). All 27 pass at exactly the Moore bound, H(13) (804,468 vertices)
included.

**Optimal non-Moore cells.** (3,5) = 56: Bar-Yehuda–Etzion's graph (two 28-cycles, F = (12,0,8,20)) rebuilt and
valid; an annealed graph of the same order is also valid. (7,3) = 80: Hafner's own adjacency list (still online) is
valid, and a Haar graph of Z5 ⋊ Z8 found here is too. Optimality: Jørgensen 1993 for 56 (secondary; alternative proof
Feria-Purón–Pineda-Villavicencio 2012, read), FMP 2013 Thm 4.1 for 80 (read).

**Delorme / Delorme–Farhi duplications (11 cells).** All rebuilt at exactly the table value
(`tools/delorme.py`, a level-lift implementation of Delorme 1985 §7):
- D = 4: W(q) with Delorme's spread {⟨X, AX⟩}, doubling A0 ⊃ A1 (§8(a)): 346, 1,734, 3,064, 4,946 for q = 5, 9, 11,
  13; tripling at q = 13 gives 5,134 = (16,4).
- D = 6: H(q) with the Hermitian spread (§8(b)): 8,992, 142,464, 374,452, 842,048 for q = 5, 9, 11, 13; tripling
  at q = 13 gives 884,062 = (16,6).
- D = 3: (16,3) = 394 = PG(2,13) plus Delorme–Farhi copies of the 14 points of a conic and of its 14 tangent lines.
  No source states this construction; it is a duplication of exactly the table's order and degree, so the value is
  reproducible, but I cannot say it is the graph the wiki had in mind.
- The (16,4) and (16,6) values are Delorme's sets with tripling (r = 2 in §7, whose printed formula is off by one).
  The paper only works q = 5; the other values are the paper's construction at other q.

**Araujo-Pardo–López and FMP (D = 3, 3 cells).** (11,3) 190, (13,3) 274, (15,3) 374 from AL's R_q, and FMP's three
Φ95 Haar graphs at (11,3): all valid.

**Hafner / Loz red cells and (3,7).** Hafner's page https://www.math.auckland.ac.nz/~hafner/bipartite/ is still online
with adjacency lists; (4,5) = 160 and (4,7) = 840 ("Bond–Delorme construction", vertex-transitive), (7,3) = 80 and
Conder's (3,7) = 168 all pass apsp.c. Copies with checksums: `lit/hafner_bipartite/`. (3,7) = 168 is also C168.1 in
Conder's census of cubic symmetric graphs (1-arc-regular, |Aut| = 504, girth 12); the census file passes too.

**"Delorme–Gómez–Quisquater" green cells.** The cited paper ("On large bipartite graphs", submitted) was never found.
- (6,7) = 8,310 and (8,7) = 40,586 are Delorme 1985 §9 (subdivide the 2q³ edges between distance 2 and 3 from an
  edge of H(q), then q copies of the distance-≤2 part; order 2q(q⁴+q³+3q²+q+1)), q = 5 and 7. Rebuilt exactly and
  valid. The wiki's green colour for these two cells points to the wrong source.
- D = 5, Δ = 10..15 (6 cells) and D = 7, Δ = 7, 9..16 (9 cells): every value is exactly (2j+1)·|GQ(q)| or
  (2j+1)·|H(q)| with Δ = q+1+j. I built 2j+1 copies of the polygon's incidence graph joined by j bijections
  points → lines (`tools/xt_build.py`; diameter ≤ n+1 for any bijections, proof in the file header). All 15 reach
  exactly the table value and pass (D = 7 by apsp_orb, up to 4,022,340 vertices). Marked "order": same order, very
  probably the same family, but the original is unavailable.
- D = 8 (Δ = 10..16 except 13): the values are Gómez's ΩH_q (1986 thesis); my rebuild has the right order but
  diameter 9 (§4, flag 1).
- (3,8) = 256: no source; the squad round found two graphs of exactly 256 (a lift of Q₃ over Z₃₂, and a Z₃₂-symmetric
  annealed graph) and one of 258 (research/squads/table-audit-r1/), all valid.
- (3,10) = 800: no source. After squad round r2 (research/squads/table-audit-r2/, closest 8), a 41-min run of the
  round-r1 Z_c-symmetric annealer (research/squads/table-audit-r1/c6/sym_anneal.c, seed 11) at b = 10 orbits,
  c = 80 found a graph of exactly 800: a Z₈₀-lift of a simple cubic bipartite graph on 5 + 5 vertices, edge orbits (a, b, t) meaning (a, i) ~ (b, i + t): (0,9,65) (0,8,23) (0,6,34)
  (1,7,11) (1,5,76) (1,8,17) (2,5,62) (2,9,55) (2,8,30) (3,6,55) (3,9,24) (3,7,49) (4,6,5) (4,7,46) (4,5,30)
  (graphs/d3D10_n800_symZ80_b10.edges.txt; apsp.c VALID, and a separate Python BFS check gives diameter 10).
- (16,5) = 27,300 and (13,8): no construction traced (§4).

**Loz orange cells (39).** No voltages, groups, base graphs or adjacency lists survive where I could reach them (thesis
restricted to Auckland logins, eyal.com.au parked, archive.org blocked here). For 13 of the 39 cells n/2 = p·k with p
prime and k | p−1, the order of a Haar graph of Z_p ⋊ Z_k, the kind of group Loz used for general graphs (cells.csv
notes give every factorization). So I tried to reach the exact table orders with Haar graphs of metacyclic groups of
order n/2 (`tools/exact_haar.py` driving research/frontier/haar_gen3, most non-abelian groups first, 30–300 s per
group; each graph rebuilt by build_haar2.py and checked by apsp.c in checks/small.txt, apsp_mt.c in
checks/haar_big.txt above 150,000 vertices, and above 10⁶ vertices by build_haar2.py plus an independent C checker,
tools/meta_haar_check.c, both doing BFS from the identity on each side, which is exact for Haar graphs since right
multiplication is transitive on each side; checks/haar_huge.txt).

<!-- LOZ -->
35 Loz cells are reached at exactly the table order (round 1: 23 of the 24 tried; round 2 went through
the rest in increasing size with the same tool, tools/exact_haar.py driving research/frontier/haar_gen3; above 10⁶
vertices each graph passes two independent two-BFS checkers, checks/haar_huge.txt):

| cell | value | group | cell | value | group |
|---|---:|---|---|---:|---|
| (3,9) | 506 | Z23 ⋊ Z11 | (8,8) | 201,480 | Z365 ⋊ Z276 |
| (4,8) | 2,184 | Z91 ⋊ Z12 | (8,9) | 1,091,232 | Z421 ⋊ Z1296 |
| (4,9) | 4,970 | Z71 ⋊ Z35 | (8,10) | 6,927,210 | Z4051 ⋊ Z855 |
| (4,10) | 11,748 | Z89 ⋊ Z66 | (9,5) | 2,496 | Z13 ⋊ Z96 |
| (5,5) | 336 | Z7 ⋊ Z24 | (9,8) | 449,480 | Z661 ⋊ Z340 |
| (5,7) | 3,110 | Z311 ⋊ Z5 | (9,9) | 2,961,536 | Z1361 ⋊ Z1088 |
| (5,8) | 9,234 | Z171 ⋊ Z27 | (9,10) | 20,017,260 | Z37069 ⋊ Z270 |
| (5,9) | 27,936 | Z97 ⋊ Z144 | (10,9) | 7,057,400 | Z25205 ⋊ Z140 |
| (5,10) | 90,068 | Z2047 ⋊ Z22 | (10,10) | 50,331,156 | Z97541 ⋊ Z258 |
| (6,5) | 684 | Z57 ⋊ Z6 | (11,9) | 15,200,448 | Z4657 ⋊ Z1632 |
| (6,8) | 29,790 | Z331 ⋊ Z45 | (11,10) | 130,592,354 | Z115979 ⋊ Z563 |
| (6,9) | 117,360 | Z815 ⋊ Z72 | (12,9) | 30,001,152 | Z4883 ⋊ Z3072 |
| (6,10) | 452,032 | Z1009 ⋊ Z224 | (12,10) | 300,383,050 | Z546151 ⋊ Z275 |
| (7,5) | 1,134 | Z63 ⋊ Z9 | (13,9) | 50,990,610 | Z14047 ⋊ Z1815 |
| (7,8) | 80,940 | Z1349 ⋊ Z30 | (14,9) | 95,087,738 | Z101807 ⋊ Z467 |
| (7,9) | 400,160 | Z2501 ⋊ Z80 | (15,9) | 168,016,334 | Z98717 ⋊ Z851 |
| (7,10) | 1,987,380 | Z11041 ⋊ Z90 | (16,9) | 288,939,118 | Z584897 ⋊ Z247 |
| (8,5) | 1,710 | Z19 ⋊ Z45 |  |  |  |

These are graphs of the table's order, not necessarily Loz's graphs. (4,8) and (4,9) are cells the repo has not
beaten, so the table value there is now backed by a checked graph. Nearly every cell tried was reached within
minutes, which makes the remaining Loz values plausible. Not reproduced: (13,10), (14,10), (15,10), (16,10).
<!-- /LOZ -->

## 4. Flags

1. **D = 8, Δ = 10..16 (green): does not check out as read.** The values 1,176,480, 2,246,940, 4,650,100,
   14,172,480 and 36,201,060 are listed verbatim in J. Gómez Martí's PhD thesis (UPC Barcelona, 1986, §2.9.3, p. 45–46)
   as N(Δ,8) ≥ |ΩH_q|, where ΩB₁ is built from 5α copies of B₁ in groups of five and 10 hub sets ("copies of K₁"),
   wired as in its Fig. 2.21 (a, b), with Δ = Δ₁ + 2 and a claimed diameter ≤ D₁ + 2. I rebuilt ΩB₁ from the figure
   (tools/omega_build.py): the order is exactly the table's (ΩH₇ has 1,176,480 vertices), but the diameter is 9.
   - H(2), H(3), every group pattern, three pairings σ: diameter 9 or 10 (apsp.c, checks/omega_D8.txt).
   - ΩH₇ at the table order: a hub has eccentricity 9 (136,080 vertices at distance 9), a copy vertex too.
   - Counting (tools/omega_bound.py): a hub of label x can only reach a point of a copy it does not touch through
     paths that keep or swap labels at hub hops; within 7 steps these reach at most 16,249 of the 19,608 points of
     H(7) (q = 8: 26,487 of 37,449; 9: 41,009 of 66,430; 11: 87,297 of 177,156; 13: 165,097 of 402,234), for any
     pairing σ. So, if hubs are joined to equally labelled vertices as in the thesis's §2.8 notation, ΩH_q has
     diameter ≥ 9 at every q in the table.
   - If every copy may be relabelled freely (the thesis does not describe this), the counting argument no longer
     applies. Annealing over such relabellings (tools/omega_anneal.c) reaches diameter 8 for H(2) (1,890 vertices,
     599 moves) but not for H(3): it stalled at 327 hub–vertex pairs at distance > 8 after 48,444 moves.
   This could be my misreading (the figure does not say which vertex each hub uses in each copy), or the
   construction in the wiki's own source (Delorme–Gómez–Quisquater, "On large bipartite graphs", never published)
   may differ. Either way these six cells have no checkable graph. (15,8) is the (14,8) value reused; the thesis also
   lists N(15,8) ≥ 14,978,080 ("ΩH₁₁d"), which the wiki does not use.
2. **No traceable construction:** 4 Loz cells (data lost), (13,8) = 5,314,680 (= 15·|H(11)| at Δ = q+2; not in
   Gómez's thesis), (16,5) = 27,300. Of these the repo has not beaten (11,10), (15,10), (16,10). (3,10) = 800 has no
   source either, but a graph of exactly that order was found here (§3), so the value now has a checked graph.
3. **Attribution:** (6,7) and (8,7) are coloured Delorme–Gómez–Quisquater on the wiki, but their construction and
   exact orders are in Delorme 1985 §9.
4. **(16,3) = 394:** no source states the construction; a Delorme–Farhi duplication on PG(2,13) gives exactly 394.

## 5. Outside the brief, for the coordinator

- **(13,5) ≥ 11,664.** Mizuno's (12,4) general graph (5,832 vertices, Comellas's table, Sept 2026,
  https://web.mat.upc.edu/francesc.comellas/delta-d/desc_g/adjacencies/adjD4/graph_d12_D4_n5832.edges, sha256
  2d276a27…a142d) doubled by B(H) (x₀ ~ y₁ iff x = y or xy ∈ E) is 13-regular, bipartite, diameter 5 on 11,664
  vertices: apsp.c VALID (checks/d13D5_n11664_BH_mizuno.txt; builder tools/closed_double.py). That is above the table
  (11,480) and above the repo's record (11,486). Found by the literature sub-agent and rebuilt here from the URL;
  research/theorems/REGULARITIES.md §1.4 had predicted it but did not have the graph. Credit: Mizuno for H.
- The repo's own copies of the table are stale: `research/frontier/heuristic.py` `TABLE` still has (13,3) = 270,
  (15,3) = 370 and None for (11,10); `research/frontier/TABLE.md` has (11,10) "unreadable" (it is 130,592,354).
- README's pending "literature check for newer values": the live wiki has no value change after March 2021 (only the
  two AL cells since 2012), and the literature sub-agent found no post-2013 paper with a larger bipartite graph in the
  range (lit/LITERATURE.md §8), apart from the (13,5) doubling above. (3,8) = 256 is unchanged.
- For the D = 8 cells (10,8), (12,8), (14,8), (16,8), which the repo has not beaten, the table value rests on a
  construction that does not check out as read (§4). A checked graph of order ≥ the table value there would settle
  it either way.
- **(11,10) = 130,592,354** (one of the three Loz cells the repo has not beaten) now has a checked graph of exactly that
  order (round 2): a Haar graph of Z115979 ⋊ Z563 (r = 110636), found by tools/meta_haar_climb.c after random sets
  gave diameter 11 (start cost 4 vertices beyond 10); meta_haar_check.c and meta_haar_bits.c both VALID
  (graphs/d11D10_n130592354_meta_115979_563_110636_x1.sol). It equals the table value, so it is not a record.
- **(3,10) = 800** is a cell the repo has not beaten. Its value had no source and no graph; there is now a checked
  graph of exactly 800 (graphs/d3D10_n800_symZ80_b10.edges.txt, §3). It equals the table value, so it is not a record.
  Going past it did not work: seven 45-min runs at 810 (c = 81) stopped at cost 2 to 6, one at 820 (c = 82) at 4
  (checks/d3D10_beyond800.txt).

## 6. The wiki's own consistency

- Percentage column: (13,3) and (15,3) still use 270 and 370 (85.98 %, 87.67 %; should be 87.26 %, 88.63 %); (15,8)
  shows 0 % (should be 6.24 %); (7,7) rounds 20.93 % down to 20.92 %.
- Upper bounds: (7,5) is 3,106 (Moore − 4) while Feria-Purón–Pineda-Villavicencio 2012 give Moore − 6 = 3,104 there
  (records/bipartite_dd/CANDIDATES.md); every other D ≥ 4 non-Moore cell uses Moore − 6. No table value exceeds its
  upper bound, and the table is monotone in Δ and in D.
- (5,7) = 3,110 equals the Moore bound of (7,5). It is the same in every revision and in the survey, and a Haar graph
  of Z311 ⋊ Z5 with exactly 3,110 vertices and diameter 7 was found here (graphs/d5D7_n3110_*.sol), so the value is
  genuine.

## 7. Round 2 (2026-10-26, table-audit-2)

Brief: decide whether any labelling makes ΩH_q diameter 8; trace (13,8), (16,5) and the small cells; rebuild what is
left. Work in `omega/` (code and NOTES.md), `lit/LITERATURE2.md`, `checks/`.

**D = 8 cells (Gómez's ΩH_q).**
- As drawn (same row label in every copy) the graph has diameter 9 at every table q: counting bound
  (tools/omega_bound.py, any pairing σ), ΩH₇ at the (10,8) order with an explicit witness pair, d(980400, 20073) = 9,
  re-checked by an independent BFS and an independent wiring check (checks/witness_omega_thesis.txt); ΩH₉ exactly 9
  on branch own-12-8. Verdict for (10,8), (11,8), (12,8), (14,8), (15,8), (16,8): **INVALID as read**.
- With a free labelling of every copy (each copy marks its own point and line per row; not in the thesis) the
  construction can reach D₁ + 2: ΩH₂ (round 1) and now **ΩH₃: 14,560 vertices, 6-regular, diameter 8**, two
  labellings found by annealing over labellings equivariant under a Singer-type automorphism of order 13
  (omega/labs/; apsp.c VALID with no symmetry assumed, and omega_verify.py re-derives the wiring from the figure;
  checks/omega_labelled.txt).
- Collineation labellings (every copy moved by an automorphism of H(q)) are the thesis's graph in disguise, so they
  have diameter 9. Identical labellings inside each block of five (plain Z₅ symmetry) are much worse than random
  ones (q = 3: 4,617 far pairs from the hub representatives against 34 for a random twisted labelling).
- q = 4 (54,600 vertices) and q = 5 (195,300): no labelling with diameter 8 found. Annealing with the twisted Z₅ ×
  Singer symmetry and eight squad variants (focused moves, steepest descent with tabu, late acceptance on a partial
  cost, greedy construction, pattern scan over block types and inner classes, closed-form affine orbit maps, GA ideas)
  all stayed near the random level: q = 4 from 18,387 to about 12,800–13,900 far pairs (390 hub representatives),
  q = 5 from 42,280 to about 35,500–38,000 (252 representatives). Squad log: research/squads/LOG.md, round
  table-audit-2-r1.
- q = 7 (the (10,8) order, 1,176,480 vertices): a random labelling with the same symmetry (Singer cube, order 19)
  leaves 6,813,773 far pairs from the 2,064 hub representatives (about 3,300 per hub); one cost evaluation takes about
  10 s here, so annealing to 0 was out of reach.
- No counting argument rules labellings out: the most a hub's routes can cover, summed, is 9.4n (q = 3), 5.5n (4),
  5.6n (5), 4.3n (7), 3.7n (9), 3.1n (13), with n the number of targets (omega/NOTES.md). For a random labelling a
  target is missed with probability about e^(−ratio), which matches the far-pair counts above and explains why q = 3
  was easy and q ≥ 4 is not.
- A first-moment estimate (omega/NOTES.md; heuristic, not a proof): with E[F] the mean number of far pairs of a
  random labelling and (n!)^(10α−1) labellings, exp(ln #labellings − E[F]) is e^(+50,000) at q = 3 but e^(−400,000)
  at q = 4 and e^(−6.4·10⁸) at q = 7. Random-like labellings should therefore not exist at the table's q; only a
  structured one could work. research/frontier/SIZE_LAW.md finds the same for Haar graphs at (10,8), (12,8), (14,8),
  (16,8).
- Verdict: the six D = 8 values have no checked graph. The construction can work in principle (q ≤ 3), but whether
  any labelling works at q = 7..13 is open; it would need a structured labelling that nobody has described.

**(13,8) and (16,5).** Still no construction. Pérez-Rosés's thesis (Newcastle 2012, Table 5.1, open on figshare)
marks the cells that came from Loz's voltage search in bold: exactly the wiki's 39 orange cells. (13,8) and (16,5) are
not bold; they are in the wiki's first revision (2012) as Delorme–Gómez–Quisquater, whose manuscript Pérez-Rosés
cites as unpublished (2011). Delorme–Gómez 2002 (EJC) could not be fetched from here (all routes in
lit/LITERATURE2.md). (13,8) = 15·|H(11)| = 5·(13,7) is not ΩH₁₁ (degree 14). **(13,8) is now reproduced at
exactly its order** by a Haar graph of PSL(2,37) × Z₁₀₅ (haar_gen3, 9 evaluations; build_haar2.py and
check_haar_indep.py VALID, graphs/d13D8_n5314680_psl_37_105.sol), so the value is attainable, though DGQ's own graph is
unknown (the repo's record there is higher anyway). (16,5) = 27,300 was not reached by Haar graphs of order 13,650
(six metacyclic groups at 120 s each, best 239 vertices unreached; research/frontier/SIZE_LAW.md puts D = 5 at Δ ≥ 10
above what Haar graphs reach), so it stays without a graph.

**Small cells.** Upper bounds are Moore − 6 for (3,7), (3,9), (4,8), (4,9), (6,5) (Feria-Purón–Pineda-Villavicencio
2012); no exhaustive search or later improvement was found. In the census of cubic vertex-transitive graphs
(≤ 1280 vertices), every bipartite one on 169–248 vertices has diameter ≥ 8 (1,825 graphs, decoded and checked here),
so **(3,7) = 168 is optimal among vertex-transitive graphs**; for (3,9) the largest vertex-transitive one of
diameter ≤ 9 has 506 vertices (graphs with stored diameter ≤ 11 rechecked here; checks/cvt_census.txt). (3,9), (4,8),
(4,9), (6,5) are bold (Loz) in Pérez-Rosés's table.

**The rest of the Loz cells.** Round 1 stopped below 3·10⁶ vertices. Round 2 ran tools/exact_haar.py (haar_gen3,
metacyclic groups of order n/2, most non-abelian first) on every remaining Loz cell in increasing size; for groups
with no element of order 2..63 (haar_gen3 has no coset speed-up there and runs out of memory), random Haar graphs
(tools/rand_meta_haar.py) and a hill climb (tools/meta_haar_climb.c) instead. Most cells fell at once, often to the
first random connection set: the table values at D = 9, 10 are far below what random Haar graphs reach, except at
the three cells the repo has not beaten. Each graph above 2·10⁷ vertices is checked by two independent low-memory
checkers written from the definitions (meta_haar_check.c, queue BFS, 9 bytes per vertex; meta_haar_bits.c, bitset
BFS, half a byte per vertex; meta_haar_pull.c, a pull BFS, for the cells above 6·10⁸ vertices), below that also by
build_haar2.py (checks/haar_huge.txt). Status per cell: see the Loz table in §3 and cells.csv.
