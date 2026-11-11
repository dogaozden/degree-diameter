# How the table records in our missing cells were built (literature)

voltage-lifts job, 2026-10-23. A literature subagent did the searching. I re-read the key quotes in the downloaded
files myself (marked **re-read**). Downloads were kept in the session scratchpad. They are not committed, because
some are third-party PDFs.

Legend:
- **READ**: the statement is in a source the agent downloaded and read. URL and quote or page are given.
- **re-read**: I also checked the quote in the downloaded text.
- **INFERRED**: my own arithmetic or reasoning, not stated in any source.
- **UNVERIFIED**: from memory or second hand, not checked.

## 1. Sources and their reliability

| source | what it gives | status |
|---|---|---|
| M. Miller, J. Širáň, *Moore graphs and beyond: a survey of the degree/diameter problem*, Electron. J. Combin. Dynamic Survey DS14v2 (2013); https://www.combinatorics.org/ojs/index.php/eljc/article/download/DS14/pdf/ | Table 4 (p. 37, "CombinatoricsWiki, accessed on 10 March 2013"); §3.4.5 on bipartite graphs (p. 36) | READ, re-read |
| CombinatoricsWiki, "The Degree Diameter Problem for Bipartite Graphs", http://combinatoricswiki.org/wiki/The_Degree_Diameter_Problem_for_Bipartite_Graphs | table values, the per-cell colour key, page history | READ over plain http: https fails certificate verification here and TLS was not bypassed, so the copy is unauthenticated. The values agree with DS14v2 Table 4 cell for cell. Colours re-read from the HTML |
| R. Feria-Purón, M. Miller, G. Pineda-Villavicencio, *On large bipartite graphs of diameter 3*, Discrete Math. 313(4) (2013) 381–390, doi:10.1016/j.disc.2012.11.013; publisher PDF on Deakin's repository, https://ndownloader.figshare.com/files/36987526 | the only published voltage assignment of a bipartite record found (§4) | READ, re-read. arXiv:1203.3588 v1 does not contain the passage |
| E. Loz, J. Širáň, *New record graphs in the degree-diameter problem*, Australas. J. Combin. 41 (2008) 63–80, https://ajc-new.maths.uq.edu.au/pdf/41/ajc_v41_p063.pdf | the voltage-lift search method (general graphs) | READ |
| H. Pérez-Rosés, *Algebraic and computer-based methods in the undirected degree/diameter problem – A brief survey*, Electron. J. Graph Theory Appl. 2(2) (2014) 166–190 | the filters in the Loz-type search | READ, title re-read |
| P. Hafner, https://www.math.auckland.ac.nz/~hafner/bipartite/ | adjacency lists, e.g. (3,7) 168 (Conder) and (4,7) 840 (Bond–Delorme) | READ |
| E. Loz, *The degree-diameter and cage problems: a study in structural graph theory*, PhD thesis, Univ. of Auckland (2009), hdl:2292/52008 | probably holds the voltage tables of the orange cells | NOT READ: full text restricted to Auckland members. Not circumvented |
| Loz's data page http://www.eyal.com.au/wiki/The_Degree/Diameter_Problem ("including adjacency lists for bipartite graphs smaller than 20,000") | adjacency lists of the orange cells below 20,000 vertices | NOT READ: the domain is parked. An archive.org snapshot exists (20231025041002), but web.archive.org is unreachable from this container. Worth opening from a normal browser |

**Page history of the wiki (READ):** the page was created on 17 Jan 2012 ("as of January 2012"). The 30 Mar 2021 edit
changed only (13,3) 270→274 and (15,3) 370→374. The 18 Feb 2022 edit added citations. **So none of our cells has
changed since January 2012.** The agent found no post-2013 bipartite record in any of our cells (Araujo-Pardo–López:
D = 3 only; Vetrík 2018: Cayley families below the table).

## 2. Who holds each missing cell (wiki colour key; READ, re-read)

Colour legend, verbatim from the wiki:
- **#bbffff**: "Bipartite Moore graphs (optimal)."
- **#CC6600**: "Graph duplications found by C. Delorme and G. Farhi."
- **#66ff66** (green): "Graphs found by C. Delorme, J. Gómez, and J. J. Quisquater." The wiki's reference is
  "Delorme, C.; Gómez, J.; Quisquater, J. J., 'On large bipartite graphs', submitted." No published version found.
- **#0066CC**: "Optimal graph found by R. Bar-Yehuda and T. Etzion and by J. Bond and C. Delorme." This is (3,5) = 56.
- **#993300**: "Graph found independently by M. Conder and R. Nedela, by C. Delorme, J. Gómez, and J. J. Quisquater
  and by Eyal Loz."
- **#ff0000** (red): "Graphs found independently by Paul Hafner and by Eyal Loz."
- **#FF9900** (orange): "Graphs found by Eyal Loz as part of the joint project *The degree/diameter problem for several
  classes of graphs* by E. Loz, H. Pérez-Rosés and G. Pineda-Villavicencio."

| D | cell (table value) | holder (colour) |
|---|---|---|
| 5 | (6,5) 684 | Loz (orange) |
| 5 | (10,5) 4000, (11,5) 5850, (12,5) 8200, (13,5) 11480, (14,5) 14760, (15,5) 20496, (16,5) 27300 | Delorme–Gómez–Quisquater (green) |
| 7 | (3,7) 168 | Conder–Nedela / DGQ / Loz (#993300) |
| 7 | (4,7) 840 | Hafner / Loz (red). Hafner's file says "vertex transitive; \|aut\|=2520; (Bond-Delorme construction)" |
| 7 | (5,7) 3110 | Loz |
| 7 | (6,7) 8310, (7,7) 23436, (8,7) 40586, (9..16,7) | DGQ (green) |
| 8 | (3,8) 256 | DGQ (green) |
| 8 | (4,8) 2184, (5,8) 9234 | Loz |
| 8 | (10,8), (11,8), (12,8), (13,8), (14,8), (15,8), (16,8) | DGQ (green) |
| 9 | (3,9) 506, (4,9) 4970, (5,9) 27936 | Loz |
| 10 | (3,10) 800 | DGQ (green) |
| 10 | (4,10) 11748, (5,10) 90068, (15,10), (16,10) | Loz |

## 3. The Loz (orange) cells: method, no data

- **DS14v2 §3.4.5, p. 36 (re-read):** "Loz, Pérez-Rosés and Pineda-Villavicencio [240] adapted the
  voltage-assignment-based method developed by Loz and Širáň [242] for general graphs to the case of bipartite graphs;
  this resulted in updating more than one third of the table of the largest known bipartite graphs."
  - [240] = "E. Loz, H. Pérez-Rosés, and G. Pineda-Villavicencio, Properties of finite metabelian groups for algebraic
    constructions, (2012) preprint." (re-read). No published version or copy was found.
  - The wiki's own citation is "E. Loz, H. Pérez-Rosés and G. Pineda-Villavicencio (2010). The degree-diameter problem
    for bipartite graphs, Combinatorics Wiki." (READ)
- **The Loz–Širáň method** (Australas. J. Combin. 41 (2008); READ):
  - Base graphs with at most 4 vertices:
    - B(s,l): bouquet with s ≤ 1 semi-edge and l loops;
    - D(l,e): dipole with l loops per vertex and e parallel edges;
    - T(l,e): K3 with l loops per vertex and e edges per pair;
    - X(l,e): K4 with l loops per vertex and e edges per pair.
  - Voltage groups: only metacyclic Z_m ⋊_r Z_n.
  - Search:
    - identity voltages on a fixed spanning tree;
    - the other voltages random, rejecting partial assignments that create multi-edges or loops;
    - the diameter computed from one vertex per fibre;
    - after a fixed number of failures, move on to the next group.
  - That paper's tables have no loopless dipole quotient, so it covers general graphs only.
  - Pérez-Rosés (EJGTA 2014, READ) adds three filters:
    - discard groups with bad properties (e.g. a large centre);
    - adapt the number of trials per group;
    - abort the diameter computation early when the girth is too small.
  - He also writes: "no detailed pseudo-code description of the algorithm has been published so far."
- **INFERRED.** A loopless dipole lifts to a bipartite graph, so the bipartite adaptation most likely used loopless
  dipoles, i.e. Haar graphs, and other loopless bipartite quotients, over metacyclic (metabelian) groups. That is the
  same family our Haar searches (haar_gen*, research/d5) already cover. This is consistent with:
  - our Haar graphs beating many orange cells, e.g. (6,8) to (6,10), (7,8) to (7,10), (8,8) to (8,10), (9,8) to
    (9,10), (10,9) to (16,9);
  - the published (7,3) Loz graph being a dipole lift (§4).
- **No voltage assignment for any orange cell in our list was found.** The likely sources are Loz's thesis
  (restricted) and his data page (offline). Both are listed in §1.

## 4. The one published bipartite voltage lift: (7,3) = 80 (exact rebuild done)

- **Feria-Purón–Miller–Pineda-Villavicencio 2013, p. 389 (re-read):** "Loz obtained the graph from a dipole (i.e., a
  two-vertex graph) with seven parallel edges and no loops as the quotient graph, and the semidirect product Z5 ⋊2 Z8
  as the voltage group. The specific values for the voltages on the parallel edges of the quotient graph were (0, 0),
  (3, 4), (4, 4), (3, 7), (3, 3), (1, 6) and (4, 6)."
  - It cites Loz's thesis, p. 72. The same paper proves that (7,3) = 80 is optimal.
- **Conventions** (Loz–Širáň 2008, READ):
  - product (a,b)(c,d) = (a + r^b c, b + d);
  - a dart u→v with voltage α gives (u,g) → (v, gα).
- **Our rebuild:**
  - lift.c uses (x,g) ~ (y, αg); g ↦ g⁻¹ converts one convention into the other, so we use α⁻¹.
  - The result is 80 vertices, 7-regular, bipartite, diameter 3, by all three checkers.
  - File: `sols/rebuild_d7D3_hafner_loz_published.txt`; checks in `verify/`.

## 5. The green (DGQ) cells: unpublished construction; a formula that reproduces them (INFERRED)

The DGQ paper "On large bipartite graphs" is listed as "submitted" and was not found. My own arithmetic (the subagent
independently noticed the same pattern):

- **Every green value at D = 5 and D = 7 equals (2j+1) · |incidence graph of a generalized polygon of order q|,
  with Δ = q + 1 + j.**
  - D = 5 uses generalized quadrangles, |GQ(q)| = 2(q+1)(q²+1):
    - (10,5) = 5·800 (q = 7);
    - (11,5) = 5·1170 (q = 8);
    - (12,5) = 5·1640 (q = 9);
    - (13,5) = 7·1640;
    - (14,5) = 9·1640;
    - (15,5) = 7·2928 (q = 11).
    - (16,5) = 27300 does **not** fit.
  - D = 7 uses generalized hexagons, |GH(q)| = 2(q+1)(q⁴+q²+1):
    - (7,7) = 3·7812 (q = 5);
    - (9,7) = 3·39216;
    - (10,7) = 3·74898;
    - (11,7) = 3·132860;
    - (12,7) = 5·132860;
    - (13,7) = 3·354312;
    - (14,7) = 5·354312;
    - (15,7) = 7·354312;
    - (16,7) = 5·804468.
    - (6,7) 8310 and (8,7) 40586 do not fit.
- **A construction that gives exactly these orders.** It is a voltage lift of
  B = (GP incidence graph) + (j perfect matchings, points → lines), with group Z_{2j+1}:
  - voltage 0 on the polygon edges;
  - voltage t on the t-th matching.
  - The matchings can be **arbitrary**.
- **Claim (proved below for generalized n-gons with n even): the lift has diameter n + 1.**
  - **Proof.** Copies are indexed by Z_{2j+1}. Write σ_t for the t-th matching. Point hops go +t; line hops go −t.
    Use two facts about generalized n-gon incidence graphs, n even:
    - same-colour distances are ≤ n;
    - opposite-colour distances are ≤ n − 1.
  - From a point s:
    - copy 0 is within n;
    - copy +t: hop first, then ≤ n more steps;
    - copy −t, point target y: walk ≤ n−1 to the line σ_t(y), then hop: ≤ n;
    - copy −t, line target y: one step to a line through s, hop, then ≤ n−1 more: ≤ n+1.
  - Lines are symmetric. ∎
- **Checked by computation:**
  - (10,5) 4000 (W(7) + 2 random matchings, Z_5);
  - (7,7) 23436 (H(5) + 1 random matching, Z_3);
  - in both, every checker gives diameter exactly n+1.
  - With Z_4 instead of Z_3, W(3) + 1 matching has diameter 6, so 2j+1 copies is tight for this voltage pattern.
- **Whether DGQ used this construction is UNVERIFIED.** It reproduces every green D = 5 and D = 7 value that fits the
  formula. "Delorme-type" multiplications of Moore graphs are a plausible origin.
- **The green D = 8 values** fit m · |GH(q)| with Δ = q + 3 and m = 30, 30, 35, 40, 45 (q = 7, 8, 9, 11, 13), and
  (13,8) = 15·|GH(11)| with Δ = q + 2. The construction is unknown.
  - Under a random model these m are about 2.5× what random voltages on GH(q) + 2 matchings could reach (RESULTS.md
    §4), so the construction must be structured.
- (3,8) 256 and (3,10) 800 (green) are not of this form.

## 6. Other adjacency lists (Hafner's page; READ, checked by the agent with BFS)

| file | order | degree | diameter | header |
|---|---|---|---|---|
| `mdec3.7` | 168 | 3 | 7 | "(Marston Conder)": the (3,7) record |
| `4.7` | 840 | 4 | 7 | "vertex transitive; \|aut\|=2520; (Bond-Delorme construction)": the (4,7) record |
| `7.3` | 80 | 7 | 3 | Hafner–Loz |
| `4.5`, `6.5`, `mdec3.10`, `4.8`, `7.5`, `8.5` | 160, 660, 720, 1650, 1000, 1596 | | | below the current records |

## 7. References for the remaining constructions (from DS14v2; READ, not opened)

- J. Bond, C. Delorme, "New large bipartite graphs with given degree and diameter", Ars Combin. 25C (1988) 123–132.
- J. Bond, C. Delorme, "A note on partial Cayley graphs", Discrete Math. 114 (1993) 63–74,
  doi:10.1016/0012-365X(93)90356-X.
- C. Delorme, "Grands graphes de degré et diamètre donnés", Europ. J. Combin. 6 (1985) 291–302,
  doi:10.1016/S0195-6698(85)80043-3.
- C. Delorme, "Large bipartite graphs with given degree and diameter", J. Graph Theory 9(3) (1985) 325–334,
  doi:10.1002/jgt.3190090304. The survey and the wiki print "8 (1985)"; Crossref gives vol. 9.
- R. Feria-Purón, G. Pineda-Villavicencio, "On bipartite graphs of defect at most 4", Discrete Appl. Math. 160 (2012)
  140–154, doi:10.1016/j.dam.2011.09.002.
- DS14v2 Table 4 prints (11,10) as "130 592 1354". The wiki has 130 592 354, which resolves TABLE.md's "unreadable"
  cell.
