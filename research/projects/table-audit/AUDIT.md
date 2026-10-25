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

Of the 112 cells (counts from cells.csv; five big checks were still running when this was written, see HANDOFF.md):

- **48 rebuilt** with the holder's own construction, or from the holder's own graph file, at exactly the table value and
  checked valid: the 27 Moore cells, (3,5), (7,3), (3,7), (4,5), (4,7), the 11 Delorme–Farhi cells, the three D = 3
  AL/FMP cells, and (6,7), (8,7) (Delorme 1985 §9).
- **26 reproduced at exactly the table order** by a construction of the same family or a graph found here, when the
  holder's own description is missing: the 15 green D = 5 and D = 7 cells (polygon covers), (3,8) (lifts found by the
  squad), and 10 Loz cells, (3,9), (4,8), (4,9), (4,10), (5,5), (5,8), (6,5), (7,5), (8,5), (9,5), as Haar graphs of
  metacyclic groups (graphs/*.sol).
- **6 do not check out as read**: (10,8), (11,8), (12,8), (14,8), (15,8), (16,8). Their values are Gómez's ΩH_q
  (PhD thesis, Barcelona 1986, §2.9.3), but that construction, as I read it, has diameter 9, not 8 (§4).
- **32 have no traceable construction**: 29 Loz cells (data lost; all have D ≥ 7), (3,10), (13,8), (16,5).

No table value was found to be wrong outright: every cell with a construction I could rebuild checks out, and no value
exceeds its upper bound. The doubtful ones are the six D = 8 cells above. Four of them, (10,8), (12,8), (14,8),
(16,8), are also cells the repo has not beaten, so the table value is the only claim there.

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
- D = 8 (Δ = 10..16 except 13): the values are Gómez's ΩH_q (1986 thesis); my rebuild has the right order but
  diameter 9 (§4, flag 1).
- (3,8) = 256: no source; the squad round found two graphs of exactly 256 (a lift of Q₃ over Z₃₂, and a Z₃₂-symmetric
  annealed graph) and one of 258 (research/squads/table-audit-r1/), all valid.
- (16,5) = 27,300, (13,8) and (3,10) = 800: no construction traced (§4).

**Loz orange cells (39).** No voltages, groups, base graphs or adjacency lists survive where I could reach them (thesis
restricted to Auckland logins, eyal.com.au parked, archive.org blocked here). Many orders have the shape 2·p·k with k
| p−1 (the order of a Haar graph of Z_p ⋊ Z_k). I tried to reach the exact table orders with Haar graphs
(`tools/exact_haar.py` driving research/frontier/haar_gen3, then build_haar2.py and apsp.c), 30 s per group, every
metacyclic group of the right order in turn: (3,9) 506 (Z23 ⋊ Z11), (4,8) 2,184 (Z91 ⋊ Z12), (4,9) 4,970 (Z71 ⋊ Z35),
(4,10) 11,748 (Z89 ⋊ Z66), (5,5) 336 (Z7 ⋊ Z24), (5,8) 9,234 (Z171 ⋊ Z27), (6,5) 684 (Z57 ⋊ Z6), (7,5) 1,134
(Z63 ⋊ Z9), (8,5) 1,710 (Z19 ⋊ Z45) and (9,5) 2,496 (Z13 ⋊ Z96) were reached exactly (graphs/*.sol, checked in
checks/small.txt). (4,8) and (4,9) are cells the repo has not beaten, so the table value there is now backed by a
checked graph. For
13 of the 39 cells n/2 = p·k with p prime and k | p−1, the order of Z_p ⋊ Z_k (cells.csv notes give every
factorization), which fits Loz's published method for general graphs (voltage lifts with metacyclic groups). That is
a pattern, not a source. (5,7) = 3,110 (one candidate group, Z311 ⋊ Z5) failed in 30 s and was being rerun longer, with
the mid-size cells (5,9), (6,8), (7,8), (5,10), (6,9), when this was written (results reach cells.csv through
tools/collect_extra.py).

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
   This could be my misreading (the figure does not say which vertex each hub uses in each copy), or the
   construction in the wiki's own source (Delorme–Gómez–Quisquater, "On large bipartite graphs", never published)
   may differ. Either way these six cells have no checkable graph. (15,8) is the (14,8) value reused; the thesis also
   lists N(15,8) ≥ 14,978,080 ("ΩH₁₁d"), which the wiki does not use.
2. **No traceable construction:** 29 Loz cells (data lost), (3,10) = 800, (13,8) = 5,314,680 (= 15·|H(11)| at
   Δ = q+2; not in Gómez's thesis), (16,5) = 27,300. Of these the repo has not beaten (3,10), (11,10), (15,10),
   (16,10).
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

## 6. The wiki's own consistency

- Percentage column: (13,3) and (15,3) still use 270 and 370 (85.98 %, 87.67 %; should be 87.26 %, 88.63 %); (15,8)
  shows 0 % (should be 6.24 %); (7,7) rounds 20.93 % down to 20.92 %.
- Upper bounds: (7,5) is 3,106 (Moore − 4) while Feria-Purón–Pineda-Villavicencio 2012 give Moore − 6 = 3,104 there
  (records/bipartite_dd/CANDIDATES.md); every other D ≥ 4 non-Moore cell uses Moore − 6. No table value exceeds its
  upper bound, and the table is monotone in Δ and in D.
- (5,7) = 3,110 equals the Moore bound of (7,5). It is the same in every revision and in the survey, and 1,555 =
  311·5 with 5 | 310, so it fits a Haar graph of Z311 ⋊ Z5. Not a copy error as far as I can tell.
