# Audit of the bipartite degree–diameter table (Δ = 3..16, D = 3..10)

Project `table-audit`, Opus lead, 2026-10-25. Brief: rebuild every entry we can, find who holds each value and the
construction, check the graph, and flag entries that do not check out or have no traceable construction.

- Per-cell results: [`cells.md`](cells.md) (table) and [`cells.csv`](cells.csv) (all fields: value, 2013 survey value,
  holder, source, construction, rebuilt, check, upper bound, Moore bound, our record, flag, notes).
- Literature notes (sources read, what is primary and what is inferred): [`lit/LITERATURE.md`](lit/LITERATURE.md).
- Checks: [`checks/`](checks/), commands in [`checks/CHECKS.md`](checks/CHECKS.md). Builders: [`tools/`](tools/).

STATUS: see the summary below; [`HANDOFF.md`](HANDOFF.md) lists what is still running or open.

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

SUMMARY_PLACEHOLDER

## 3. What was rebuilt, family by family

Every rebuilt graph was written as an edge list and checked by `research/lifts/coordinator_check/apsp.c` (all-pairs,
no symmetry), by `apsp_mt.c` (the same with threads), or, for the level covers, by `apsp_orb.c` (BFS from one level
plus a check, edge by edge, that the level shift is an automorphism). The builders are mine (tools/), except the
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
- (16,5) = 27,300, the D = 8 cells (Δ = 10..16), (3,8) = 256 and (3,10) = 800: no construction traced (§4).

**Loz orange cells (39).** No voltages, groups, base graphs or adjacency lists survive where I could reach them (thesis
restricted to Auckland logins, eyal.com.au parked, archive.org blocked here). Many orders have the shape 2·p·k with k
| p−1 (the order of a Haar graph of Z_p ⋊ Z_k). I tried to reach the exact table orders with Haar graphs
(`tools/exact_haar.py` driving research/frontier/haar_gen3, then build_haar2.py and apsp.c): LOZ_PLACEHOLDER

## 4. Flags

FLAGS_PLACEHOLDER

## 5. Outside the brief, for the coordinator

- **(13,5) ≥ 11,664.** Mizuno's (12,4) general graph (5,832 vertices, Comellas's table, Sept 2026,
  https://web.mat.upc.edu/francesc.comellas/delta-d/desc_g/adjacencies/adjD4/graph_d12_D4_n5832.edges, sha256
  2d276a27…a142d) doubled by B(H) (x₀ ~ y₁ iff x = y or xy ∈ E) is 13-regular, bipartite, diameter 5 on 11,664
  vertices: apsp.c VALID (checks/d13D5_n11664_BH_mizuno.txt; builder tools/closed_double.py). That is above the table
  (11,480) and above the repo's record (11,486). Found by the literature sub-agent and rebuilt here from the URL;
  research/theorems/REGULARITIES.md §1.4 had predicted it but did not have the graph. Credit: Mizuno for H.
- The repo's own copies of the table are stale: `research/frontier/heuristic.py` `TABLE` still has (13,3) = 270,
  (15,3) = 370 and None for (11,10); `research/frontier/TABLE.md` has (11,10) "unreadable" (it is 130,592,354).

## 6. The wiki's own consistency

- Percentage column: (13,3) and (15,3) still use 270 and 370 (85.98 %, 87.67 %; should be 87.26 %, 88.63 %); (15,8)
  shows 0 % (should be 6.24 %); (7,7) rounds 20.93 % down to 20.92 %.
- Upper bounds: (7,5) is 3,106 (Moore − 4) while Feria-Purón–Pineda-Villavicencio 2012 give Moore − 6 = 3,104 there
  (records/bipartite_dd/CANDIDATES.md); every other D ≥ 4 non-Moore cell uses Moore − 6. No table value exceeds its
  upper bound, and the table is monotone in Δ and in D.
- (5,7) = 3,110 equals the Moore bound of (7,5). It is the same in every revision and in the survey, and 1,555 =
  311·5 with 5 | 310, so it fits a Haar graph of Z311 ⋊ Z5. Not a copy error as far as I can tell.
