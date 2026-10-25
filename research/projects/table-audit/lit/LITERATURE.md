# Literature audit of the bipartite degree–diameter table (Δ = 3..16, D = 3..10)

Literature sub-agent for project `table-audit`, 2026-10-25. Scope: who built each table graph and how, from sources
reachable from the cloud container. Downloaded PDFs and texts are in the session scratchpad, not in the repo. The only
data copied into the repo is Paul Hafner's surviving page of bipartite adjacency lists (`hafner_bipartite/`, see §4).

Labels used below:
- **[read]**: I read the full text (or the cited pages) of the primary source.
- **[secondary]**: I only have it through a survey, a citing paper, an abstract or the wiki.
- **[inferred]**: my arithmetic or computation, not stated in any source I read.
- **[checked]**: I rebuilt or downloaded the graph and ran a BFS check here (Python for small graphs; for 11,664
  vertices I compiled `research/lifts/coordinator_check/apsp.c`). These are quick checks, not coordinator checks.

## 0. The table itself

- Live wiki page, read over plain http on 2026-10-25 (oldid 649, last edited 18 Feb 2022 by user Guillermo). I parsed
  the cell colours from the HTML. They match the brief's groups exactly. **[read]**
- Page history has four revisions: 17 Jan 2012 (oldid 296, imported, author "Gpineda"), 3 Jan 2019 (297), 30 Mar 2021
  (524), 18 Feb 2022 (649). I diffed the table of each revision against the current one. The only changes since
  January 2012 are (13,3) 270 → 274 and (15,3) 370 → 374, recoloured from Delorme–Farhi to "Araujo and López". Every
  other value and colour, including (5,7) = 3,110 and (11,3) = 190 (already yellow in 2012), is the same as in Jan 2012.
- Miller–Širáň, DS14v2 (2013), Table 4 (p. 37), "CombinatoricsWiki, accessed on 10 March 2013", has the same values
  as the Jan 2012 revision. Its (11,10) reads "130 592 1354", a typo: the wiki has **130,592,354** in every revision.
  https://www.combinatorics.org/ojs/index.php/eljc/article/download/DS14/pdf/ **[read]**
- The wiki's upper-bound table shows "0%" for (15,8). The order there (14,172,480) is the (14,8) graph reused (maximum
  degree 14 ≤ 15), so this is a formula glitch on the page, not a different graph.
- The wiki has no data files for this table. Its "several classes of graphs" project page is a one-line stub
  (rev. 293). Special:ListFiles lists only one PDF (Pelekhaty, general graphs).

## 1. Delorme–Gómez–Quisquater (green cells)

### (a) Sources

- Wiki reference: C. Delorme, J. Gómez, J. J. Quisquater, "On large bipartite graphs", submitted. **I found no
  published version or preprint.** Searches I ran: web search on the title and author combinations; arXiv API; the
  Comellas mirror `web.mat.upc.edu/francesc.comellas/old-files/delta-d/papers/` (directory listing read; it has
  Delorme 1985 EJC, Delorme–Farhi 1984, Gómez–Fiol 1985, Gómez–Fiol–Serra 1993, Comellas–Gómez 1995, Gómez's 1986
  thesis, Bermond–Delorme–Quisquater 1992 table, Loz–Širáň 2008, and no DGQ paper); Unpaywall. The survey DS14v2
  §3.4.5 does not mention DGQ. Its reference [127] is Delorme–Quisquater, "Some new large compound graphs", LRI
  Internal Report 317, December 1986. That report is not online.
- Delorme–Gómez, "Some new large compound graphs", Europ. J. Combin. 23 (2002) 539–547, doi:10.1006/eujc.2002.0581.
  Unpaywall says it is free at the publisher (Elsevier open archive), but ScienceDirect returns 403 to curl and to
  WebFetch, and CORE's API was rate-limited. **Not read.** Someone on a normal browser can get it from the DOI.
- Gómez–Fiol–Serra, "On large (Δ,D)-graphs", Discrete Math. 114 (1993) 219–235 **[read]**. Its compounds of
  bipartite Moore graphs are for general graphs, not bipartite ones. Comellas–Gómez 1995 (arXiv math/9411218)
  **[read]** is also about general graphs.
- Delorme, "Grands graphes de degré et diamètre donnés", Europ. J. Combin. 6 (1985) 291–302 **[read in full]**
  (Comellas mirror `papers/81981341.pdf`, a CORE/Elsevier copy). Two of the "DGQ" cells come from its §9 (see below).

### (b) Constructions per cell

**(6,7) = 8,310 and (8,7) = 40,586: Delorme 1985 EJC §9, "Insertion de sommets sur les arêtes". [read, exact match]**
Take the incidence graph G of a generalized hexagon of order q and fix an edge (u,v). On every edge (a,b) with
inf(d(a,u), d(a,v)) = 2 and inf(d(b,u), d(b,v)) = 3, insert a new vertex: "Il y a ainsi 2q³ nouveaux sommets, et le
degré n'a pas augmenté." The diameter becomes 7. Then let A0 be the vertices with inf(d(x,u), d(x,v)) ≤ 2. Its
neighbourhood is exactly the set of new vertices, and "on pourra dédoubler A0 à q − 1 reprises sans modifier le
degré ni le diamètre" (the new vertices have degree 2, so q − 1 copies of A0 can be added). The paper states the
order:

  2(q+1)(q⁴+q²+1) + 2q³ + (q−1)·2(q²+q+1) = 2q(q⁴+q³+3q²+q+1), degree q+1, diameter 7, bipartite, 2-connected.

q = 5 gives 10·831 = **8,310** (Δ = 6). q = 7 gives 14·2,899 = **40,586** (Δ = 8). Both match the table exactly. The
paper itself only works the example q = 2 (156 vertices). So the wiki's green colour for these two cells points to the
wrong paper; the construction is Delorme 1985 §9. (q = 3 gives 834 and q = 4 gives 2,984. Both are below the table's
(4,7) = 840 and (5,7) = 3,110.)

**The other D = 5 and D = 7 cells (no primary source found).** The values are (2j+1)·|P| for a generalized
quadrangle (D = 5) or hexagon (D = 7) P of order q, with Δ = q+1+j. **[inferred, exact arithmetic]**

| cell | value | decoding |
|---|---|---|
| (10,5) | 4,000 | 5·|GQ(7)| = 5·800, j = 2 |
| (11,5) | 5,850 | 5·|GQ(8)| = 5·1,170, j = 2 |
| (12,5) | 8,200 | 5·|GQ(9)| = 5·1,640, j = 2 |
| (13,5) | 11,480 | 7·|GQ(9)|, j = 3 |
| (14,5) | 14,760 | 9·|GQ(9)|, j = 4 |
| (15,5) | 20,496 | 7·|GQ(11)| = 7·2,928, j = 3 |
| (7,7) | 23,436 | 3·|H(5)| = 3·7,812, j = 1 |
| (9,7) | 117,648 | 3·|H(7)|, j = 1 |
| (10,7) | 224,694 | 3·|H(8)|, j = 1 |
| (11,7) | 398,580 | 3·|H(9)|, j = 1 |
| (12,7) | 664,300 | 5·|H(9)|, j = 2 |
| (13,7) | 1,062,936 | 3·|H(11)|, j = 1 |
| (14,7) | 1,771,560 | 5·|H(11)|, j = 2 |
| (15,7) | 2,480,184 | 7·|H(11)|, j = 3 |
| (16,7) | 4,022,340 | 5·|H(13)| = 5·804,468, j = 2 |

The degree gain (k−1)/2 for k copies is the out-degree of a regular tournament on k vertices. Comellas's operation
list cites a compound "B(T): compound using a bipartite graph B and a tournament T", from Gómez–Fiol, "Dense
compound graphs", Ars Combin. 20-A (1985) 211–237. That PDF is on the Comellas mirror but is a scan without a text
layer, and I did not read it. So the link to B(T) is a guess. The repo already proves this (2j+1)·|polygon| law
(research/theorems/REGULARITIES.md, item 4), so these cells can be rebuilt without the paper.

**(16,5) = 27,300 does not fit the law.** 27,300 = 10·13·14·15 = 10·q(q+1)(q+2) with q = 13. That is only arithmetic,
not a construction. **[inferred]** The repo already has (16,5) ≥ 31,460 (A4 flag graph over GF(3)).

**D = 8 (seven green cells).** **[inferred]** The decoding below matches the repo's formula
(2j+1)·(⌊(q−1)/2⌋ + 3(j−1))·|H(q)|, Δ = q+1+j.

| cell | value | decoding |
|---|---|---|
| (10,8) | 1,176,480 | 30·|H(7)|, q = 7, j = 2, 30 = 5·(3+3) |
| (11,8) | 2,246,940 | 30·|H(8)|, q = 8, j = 2, 30 = 5·(3+3) |
| (12,8) | 4,650,100 | 35·|H(9)|, q = 9, j = 2, 35 = 5·(4+3) |
| (13,8) | 5,314,680 | 15·|H(11)|, q = 11, j = 1, 15 = 3·5 |
| (14,8) | 14,172,480 | 40·|H(11)|, q = 11, j = 2, 40 = 5·(5+3) |
| (15,8) | 14,172,480 | same graph as (14,8) |
| (16,8) | 36,201,060 | 45·|H(13)|, q = 13, j = 2, 45 = 5·(6+3) |

No source I could reach describes this construction.

**(3,8) = 256 and (3,10) = 800 (green): no source found.** Neither is a symmetric cubic graph. In Conder's census of
cubic symmetric graphs up to 10,000 vertices, the largest bipartite one of diameter 8 has 216 vertices (C216.2) and
of diameter 10 has 720 (C720.3, the Conder graph on Hafner's page, §4). For comparison, Bar-Yehuda–Etzion 1992 (§6)
give 248 for (3,8) and 672 for (3,10), and Hafner's page gives 720 for (3,10).

### (c) Not found

The DGQ paper; the Delorme–Quisquater 1986 LRI report; the full text of Delorme–Gómez 2002. Without these I have no
source for the D = 5, D = 7 (except (6,7) and (8,7)) or D = 8 green cells, nor for (3,8), (3,10) or (16,5).

## 2. Delorme–Farhi duplications (brown cells)

### (a) Sources

- C. Delorme, "Grands graphes de degré et diamètre donnés", Europ. J. Combin. 6 (1985) 291–302, §7–8. **[read]**
  ScienceDirect pii S0195669885800433; text from the Comellas mirror (a CORE copy).
- C. Delorme, G. Farhi, "Large graphs with given degree and diameter – Part I", IEEE Trans. Comput. C-33 (1984)
  857–860. **[read]** (Comellas mirror, `DeFa84-IEEETransComp-c33-857_860.pdf`.) It has only the general-graph
  duplication: "N(Δ+1,D) ≥ N(Δ,D) + ⌈N(Δ,D)/(Δ²+1)⌉ … add t new vertices yi, with yi adjacent to xi and to the
  neighbors of xi", where the xi are pairwise at distance ≥ 3. The bipartite cells come from Delorme 1985 §7–8.
- C. Delorme, "Large bipartite graphs with given degree and diameter", J. Graph Theory 9 (1985) 325–334,
  doi:10.1002/jgt.3190090304. Not open access (Unpaywall). **Not read.**

### (b) The general operation, Delorme 1985 §7 [read, p. 297–298]

Take a chain of induced subgraphs A0 ⊃ A1 ⊃ A2 ⊃ … such that:
- (a) N(A_{i+1}) ⊆ A_i, and each vertex of A_i − A_{i+1} is adjacent to at most one vertex of A_{i+1};
- (b) each vertex of G − A0 is adjacent to at most one vertex of A0;
- (c) each component B of A0 has, for all x, y in B, some z outside A0 with d(x,z) + d(y,z) ≤ D.

Doubling A0, then A1 in A0 and in its copy, and so on, gives degree Δ+1, the same diameter, and
|G| + |A0| + 2|A1| + 4|A2| + … vertices. A graph built from a bipartite G stays bipartite. A copy is joined to the
G-neighbours of its original.

For a larger degree gain the paper says: "Pour avoir une augmentation de r du degré, on pourra 'dé-r+1-upler', ce
qui amène une augmentation du nombre de sommets de (r−1)(A0 + rA1 + ··· r^i A_i + ···)." Its own example (9-cycle,
degree 4, 25 vertices) only works if the printed formula is off by one. Read it as: (r+1)-upling raises the degree
by r and adds r(|A0| + (r+1)|A1| + (r+1)²|A2| + …) vertices. For r = 2 (tripling, Δ+2) that is
2(|A0| + 3|A1| + 9|A2|).

### (c) The sets, Delorme 1985 §8 [read]

**§8(a), generalized quadrangle W(q).** Points are those of PG(3,q). The lines on X0 are the lines through X0 in
the plane x0·y − y0·x − z0·t + t0·z = 0. Choose a, b with T² − aT + b² irreducible, and let
A = [[a, −b],[b, 0]] ⊗ I2. The lines {X, AX} then form a spread of q²+1 lines, pairwise at distance 4 in the
incidence graph. Take A1 = one spread line and A0 = A1's neighbourhood plus the q²+1 spread lines, so
|A0| = q²+q+2 and |A1| = 1. Doubling adds q²+q+4. Example in the paper: q = 5, 312 + 34 = **346**.
- Doubling (Δ = q+2): 2(q+1)(q²+1) + q²+q+4. q = 5, 9, 11, 13 gives 346, 1,734, 3,064, 4,946. These match (7,4),
  (11,4), (13,4) and (15,4). The paper states only q = 5. **[read + inferred]**
- **(16,4) = 5,134 [inferred, exact]:** tripling with q = 13: 4,760 + 2(184 + 3·1) = 4,760 + 374 = 5,134. This is
  the same chain as §8(a) with r = 2 in §7. No source states q = 13 or tripling.

**§8(b), generalized hexagon** (citing Thas 1980 for q³+1 vertices pairwise at distance 6). A2 = one of these
vertices; A1 = the neighbourhood of A2 plus the q³+1 vertices; A0 = A1 plus its neighbourhood. Then |A2| = 1,
|A1| = q³+q+2 and |A0| = q⁴+2q³+q²+2q+2. Example in the paper: q = 5, 7,812 + 912 + 2(132) + 4 = **8,992**.
- Doubling (Δ = q+2), q = 5, 9, 11, 13: 8,992; 132,860 + 8,120 + 1,480 + 4 = 142,464; 374,452; 842,048. These match
  (7,6), (11,6), (13,6) and (15,6). **[read + inferred]**
- **(16,6) = 884,062 [inferred, exact]:** tripling with q = 13, |A0| = 33,152, |A1| = 2,212, |A2| = 1:
  804,468 + 2(33,152 + 3·2,212 + 9·1) = 804,468 + 79,594 = 884,062.

**(16,3) = 394: not confirmed.** 394 = 2(q²+q+1) + 28 = 366 + 2(q+1) with q = 13 (PG(2,13) incidence graph and
Δ = q+3). **[inferred]** One tripling of PG(2,13) cannot give it. With A1 = ∅, condition (b) plus "every vertex of
A0 has at most one neighbour in A0" (needed to keep Δ ≤ q+3) forces A0 to have at most one point and one line, so
at most 2 vertices and 4 added. I also tried a few hand-made 394-vertex variants on PG(2,13): copy the 14 points of a
line and the 14 lines through a point, with or without some edges. None gave Δ = 16 with D = 3 [checked]. The
source is probably Delorme's 1985 JGT paper or Bond–Delorme 1988, neither of which I could read. Related fact: the
values that were in the table before 2013, (11,3) = 186, (13,3) = 270 and (15,3) = 370, are 2(q²+q+3) for
q = 9, 11, 13. FMP 2013 says their 190 "improves by 4 vertices the previous lower bound for Nb(11,3)", and the Jan
2012 wiki colours 270 and 370 as Delorme–Farhi.

### (d) Not found

The JGT 1985 paper. The exact (16,3) construction.

## 3. Eyal Loz (orange cells)

### (a) Sources

- E. Loz, PhD thesis, "The degree-diameter and cage problems: a study in structural graph theory", University of
  Auckland, 2009. Handle https://hdl.handle.net/2292/52008. The OAI-PMH record (read through
  `researchspace.auckland.ac.nz/server/oai/request`) says: "**Restricted Item. Full text is available to
  authenticated members of The University of Auckland only.**" The file is `loz-2009-whole.pdf`, 5,665,387 bytes,
  bitstream 42683a48-0599-4547-89cb-438622c75421. All four bitstreams return HTTP 401. I did not try to get around
  this. The abstract says the findings are split into "the general class, the bipartite class and the Cayley class"
  and that the thesis generalizes the upper bound for abelian lifts of dipoles. **[secondary: abstract only]**
- Handle 2292/3513 (which the brief suggested) is not Loz. It is Hafner's CDMTCS report 004 (1995), "Large Cayley
  graphs and digraphs with small degree and diameter", open access, 6 pages, read. It covers general Cayley graphs
  only, with nothing bipartite.
- DS14v2 ref. [240]: E. Loz, H. Pérez-Rosés, G. Pineda-Villavicencio, "Properties of finite metabelian groups for
  algebraic constructions", 2012 preprint. Not found anywhere (web, arXiv, Pineda-Villavicencio's 2011 research
  statement). The survey sentence is: they "adapted the voltage-assignment-based method developed by Loz and Širáň
  [242] for general graphs to the case of bipartite graphs; this resulted in updating more than one third of the
  table". **[read, survey]**
- Loz–Širáň, Australas. J. Combin. 41 (2008) 63–80 **[read]**: general graphs only. Voltage graphs on small base
  graphs with groups Z_m ⋊_r Z_n, found by random search.
- Loz's data: www.eyal.com.au returns 403 (parked). His Auckland page, https://www.math.auckland.ac.nz/~eloz002/,
  is still up but has no data. Comellas's D = 7 page links an archived copy at
  `https://web.archive.org/web/20160315000000*/http://www.eyal.com.au/wiki/The_Degree/Diameter_Problem`. That host
  is blocked here. **The coordinator's Mac may be able to fetch Loz's bipartite page and adjacency lists from it**,
  probably under `.../wiki/The_Degree/Diameter_Problem_for_Bipartite_Graphs`. Comellas hosts Loz's general-graph
  adjacency lists (e.g. `delta-d/desc_g/adjacencies/adjD7/Loz_1320.txt`), but none for bipartite graphs.
- Guillermo Pineda-Villavicencio's site (guillermo.com.au) is behind a Cloudflare challenge. FMP 2013 says their
  (11,3) adjacency lists were posted there.

### (b) Per-cell construction

**Not found for any cell.** No base graphs, groups or voltages. What follows is only a pattern in the orders.
**[inferred]**

For 13 of the 39 orange cells, n/2 = p·k with p prime and k dividing p − 1. That is exactly the order of a
metacyclic group Z_p ⋊_r Z_k with r of order k mod p, the kind of group Loz used for general graphs. So many of
these are probably dipole lifts (Haar graphs, two base vertices) or other lifts over such groups. Examples:
(3,9) 506 = 2·23·11; (4,9) 4,970 = 2·71·35; (5,7) 3,110 = 2·311·5; (6,5) 684 = 2·19·18;
(11,10) 130,592,354 = 2·115,979·563; (12,10) 2·546,151·275; (13,10) 2·721,181·428; (14,9) 2·101,807·467;
(14,10) 2·2,056,741·295; (15,9) 2·98,717·851; (15,10) 2·2,277,551·505; (16,9) 2·584,897·247;
(16,10) 2·1,934,041·1,065.

For the other cells k does not divide p − 1, so they would need a composite modulus or a larger base graph:
(4,8) 2,184 = 2·1,092; (4,10) 2·89·66; (5,5) 336 = 2·168; (5,8) 2·19·243; (5,9) 2·97·144; (5,10) 2·89·506
(or 2·2,047·22 with 2,047 = 23·89); (6,8) 2·331·45; (6,9) 2·163·360; (6,10) 2·1,009·224; (7,5) 2·7·81;
(7,8)–(7,10); (8,5) 2·19·45; (8,8)–(8,10); (9,5) 2·13·96; (9,8)–(9,10); (10,9), (10,10); (11,9); (12,9); (13,9).

The full factor list is reproducible from the table with a one-line factorization.

### (c) (5,7) = 3,110

I see no sign of a copy error.
- 3,110 is in the Jan 2012 wiki revision, the 2013 survey (Table 4) and the current page. The wiki's own percentage
  column is consistent with it: 3,110/10,916 = 28.49%.
- 3,110/2 = 1,555 = 311·5 with 5 | 310, the clean Z_311 ⋊ Z_5 pattern above. A 5-regular Haar graph of a group of
  order 1,555 would have exactly this order.

The Moore-bound coincidence with (7,5) looks accidental. Loz's Jan 2009 table (eyal.com.au) could not be read. I
found no source older than 2012 that lists (5,7).

### (d) Not found

Voltages, groups or base graphs for every Loz cell. The thesis is restricted. The metabelian preprint and Loz's own
data page are unreachable from here.

## 4. Hafner and Loz independently (red): (4,5) = 160, (4,7) = 840, (7,3) = 80

### (a) Sources

- **Paul Hafner's page "Some large bipartite graphs": https://www.math.auckland.ac.nz/~hafner/bipartite/ (still
  online).** **[read, checked]** It lists:

| file | order, degree, diameter | Hafner's note |
|---|---|---|
| `mdec3.7` | 168, 3, 7 | Marston Conder |
| `mdec3.10` | 720, 3, 10 | Marston Conder |
| `4.5` | 160, 4, 5 | "vertex transitive; \|aut\|=160; (Bond-Delorme construction; must be Cayley!)" |
| `4.7` | 840, 4, 7 | "vertex transitive; \|aut\|=2520; (Bond-Delorme construction)" |
| `4.8` | 1,650, 4, 8 | "not vertex transitive; \|aut\|=825; (Bond-Delorme construction)" |
| `6.5` | 660, 6, 5 | not vertex-transitive, \|aut\| = 330, Bond-Delorme |
| `7.5` | 1,000, 7, 5 | not vertex-transitive, \|aut\| = 500, Bond-Delorme |
| `8.5` | 1,596, 8, 5 | not vertex-transitive, \|aut\| = 798, Bond-Delorme |
| `7.3` | 80, 7, 3 | no header; this is the URL FMP 2013 cite as "E. Loz and P. Hafner, A bipartite (7,3,−6)-graph, personal communication 2010" |

- I downloaded all nine files and copied them to `research/projects/table-audit/lit/hafner_bipartite/`. Each line is
  one vertex's neighbour list, 0-based, with optional `#` header lines; `mdec3.10` is 1-based. A Python BFS confirmed
  every one is symmetric, regular of the stated degree, bipartite with equal sides, and has exactly the stated
  diameter **[checked]**:
  7.3 → 80/7/3, 4.5 → 160/4/5, 4.7 → 840/4/7, 4.8 → 1,650/4/8, 6.5 → 660/6/5, 7.5 → 1,000/7/5, 8.5 → 1,596/8/5,
  mdec3.7 → 168/3/7 (girth 12), mdec3.10 → 720/3/10.
  The red cells, and (3,7), can therefore be rebuilt straight from these files. 4.8, 6.5, 7.5, 8.5 and mdec3.10 are
  below the current table values (2,184; 684; 1,134; 1,710; 800).
- Hafner's notes say the (4,5) and (4,7) graphs come from the **Bond–Delorme partial Cayley graph construction**:
  J. Bond, C. Delorme, "New large bipartite graphs with given degree and diameter", Ars Combin. 25C (1988) 123–132,
  and "A note on partial Cayley graphs", Discrete Math. 114 (1993) 63–74, doi:10.1016/0012-365X(93)90356-X. Neither
  was read: Ars Combin. is not online, and ScienceDirect blocks scripted access.
- Hafner, "Large Cayley graphs and digraphs with small degree and diameter" (CDMTCS-004, 1995; also in Computational
  Algebra and Number Theory, Kluwer 1995, 291–302) **[read]**: general graphs only.
- The (7,3) graph is optimal. Feria-Purón, Miller, Pineda-Villavicencio, "On large bipartite graphs of diameter 3",
  Discrete Math. 313 (2013) 381–390, arXiv:1203.3588 **[read]**, prove there is no bipartite (7,3,−4)-graph
  (Theorem 4.1), "therefore Nb(7,3) = 80". The (7,3,−2) case is excluded by Delorme–Jørgensen–Miller–
  Pineda-Villavicencio, J. Graph Theory 61 (2009) 271–288 (cited there, not read).

## 5. (3,7) = 168

- Conder's census of cubic symmetric graphs (https://www.math.auckland.ac.nz/~conder/symmcubic2048list.txt and
  symmcubic10000list.txt) **[read]** has three bipartite graphs on 168 vertices:
  - **C168.1: |Aut| = 504, type 1 (1-arc-regular), girth 12, diameter 7, bipartite.** This is the table graph.
  - C168.2: girth 6, diameter 12.
  - C168.6: girth 12, diameter 8.

  C168.1 is the largest bipartite cubic symmetric graph of diameter 7 in the census (C162.1 and C144.1 come next).
- Hafner's file `mdec3.7` ("a bipartite graph of order 168, degree 3, diameter 7 (Marston Conder)") is cubic,
  bipartite, diameter 7 and girth 12 **[checked]**. That fits C168.1, though I did not test isomorphism. Conder's
  edge sets are in `~conder/AllSymmCubic-OrderUpTo10000-ByEdgeSets.txt(.gz)` (not downloaded). I did not look up the
  Foster-census letter for C168.1.
- Conder–Nedela: the wiki cites a 2006 preprint, "A more detailed classification of symmetric cubic graphs". It was
  published as "A refined classification of symmetric cubic graphs", J. Algebra 322 (2009) 722–740. Not read.

## 6. (3,5) = 56 and the optimality proofs

**R. Bar-Yehuda, T. Etzion**, "Connections between two cycles – a new design of dense processor interconnection
networks", Discrete Appl. Math. 37/38 (1992) 29–43. Scanned PDF from Etzion's site,
https://etzion.net.technion.ac.il/files/2016/02/P24.pdf. **[read: §2 and Appendix B page images]**

The construction (§2): take two n-cycles on vertices (i,0) and (i,1), i ∈ Z_n. Choose s dividing n and Δ−2 functions
F on {0, …, s−1} such that F(i)+i mod s is a permutation. For each F add the edges (j,0)–((j + F(j mod s)) mod n, 1).
Appendix B, "Graphs which attain the bounds of Table 2" (the bipartite table), gives the parameters below. I rebuilt
each one **[checked]**:

| cell | n | F | result |
|---|---|---|---|
| (3,5) = 56 | 28 | (12, 0, 8, 20), s = 4 | bipartite, cubic, diameter 5 |
| (3,8) = 248 | 124 | (48, 92, 80, 28) | bipartite, cubic, diameter 8 (table now 256) |
| (3,10) = 672 | 336 | (77, 63, 39, 125, 301, 175, 221) | bipartite, cubic, diameter 10 (table now 800) |
| (4,5) = 152 | 76 | (65, 25, 41, 9) / (57, 13, 33, 73) | bipartite, 4-regular, diameter 5 (table now 160) |

Appendix B also lists (4,8) = 1,540, (4,9) = 3,440, (4,10) = 8,000, (5,5) = 280, (5,8) = 6,100, (5,9) = 19,000 and
(5,10) = 60,000. All are below today's table.

- Bond–Delorme 1988 (Ars Combin. 25C) is the other source the wiki names for 56. Not read.
- **Optimality of 56:** L. K. Jørgensen, "Nonexistence of certain cubic graphs with small diameters", Discrete Math.
  114 (1993) 265–273, doi:10.1016/0012-365X(93)90371-Y. Cited for this by DS14v2 §3.4.4 ("whose optimality was
  proved by Jørgensen [216]") and by FMP 2013. Not read. An alternative proof: Feria-Purón and Pineda-Villavicencio,
  "On bipartite graphs of defect at most 4", Discrete Appl. Math. 160 (2012) 140–154, arXiv:1010.5651 **[read §6]**.
  "The results of this paper, combined with those of [11 = Jørgensen], assert that there are no bipartite
  (3,D,−4)-graphs with D ≥ 5, outcome that gives an alternative proof of the optimality of the known bipartite
  (3,5,−6)-graph (see [4 = Bond–Delorme])."
- **Optimality of 80 for (7,3):** FMP 2013, see §4.

## 7. (11,3) = 190, (13,3) = 274, (15,3) = 374

- **FMP 2013** (arXiv:1203.3588, Discrete Math. 313 (2013) 381–390) **[read]**. §5 defines Φ_m(a1, …, a_{d−3}):
  vertices x_i, y_i for i ∈ Z_m, and edges x_i ~ y_i, y_{i+1}, y_{i−1}, y_{i+a_j}. This is the Haar graph of Z_m with
  connection set {0, 1, −1, a1, …, a_{d−3}}. Their three (11,3) graphs on 190 vertices:
  - Φ95(4, 7, 16, 27, 38, 52, 62, 81)
  - Φ95(4, 16, 30, 43, 51, 62, 71, 89)
  - Φ95(11, 15, 21, 28, 37, 40, 45, 63)
- **Araujo-Pardo–López**, "On new record graphs close to bipartite Moore graphs", arXiv:2005.02427 **[read §3]**;
  published in Graphs and Combinatorics (2022), which I did not check. Theorem 1: "Let q be a power of prime, then
  there exists a (q+2)-bipartite graph of diameter 3 and order 2(q²+q+5)". The graph R_q is built from the PG(2,q)
  incidence graph by deleting edges, adding new vertices, and finally adding a matching. q = 9, 11, 13 gives 190,
  274 and 374, which matches the wiki (190 yellow, shared with FMP; 274 and 374 pink). The repo's research/plus2/
  already covers this.

## 8. Changes after 2013

- **The live wiki page has not changed since Feb 2022.** The only post-2012 edits are the two AL cells (§0).
- No published paper after 2013 that I found claims a larger bipartite (Δ,D) graph in this range. I searched the web,
  the arXiv API for "bipartite" with "degree/diameter", "bipartite Moore" and "biregular", and looked at
  Araujo-Pardo–Dalfó–Fiol–López 2024 (arXiv:2404.04680, biregular, D = 3, a different problem), Comellas
  arXiv:2406.18994 (general graphs), and Cames van Batenburg–Korsky arXiv:2608.03965.
  - Cames van Batenburg–Korsky (2026), "Asymptotically attaining the Moore bound" **[read relevant parts]**: general
    graphs H_{k,q} on partial flags of F_q^{2k+1}, with an asymptotic result only. Their §4 uses the bipartite
    graph B(H) (x0 ~ y1 iff x = y or xy ∈ E(H)), but for line-graph diameter, not for table values.
- **A new consequence of a 2026 general-graph record [checked]:**
  - The Comellas general table (live page, updated to Oct 2026) has (12,4) = 5,832 by Ryosuke Mizuno (25 Sep 2026),
    with an edge list at
    https://web.mat.upc.edu/francesc.comellas/delta-d/desc_g/adjacencies/adjD4/graph_d12_D4_n5832.edges
    (also github.com/rmizuno42/ddp, results/degree12-diameter4).
  - The repo already notes that 2·5,832 = 11,664 would beat (13,5) = 11,480 but says "We do not have that graph"
    (research/theorems/REGULARITIES.md).
  - I downloaded it (5,832 vertices, 34,992 edges). The repo's apsp.c gives 12-regular, diameter 4, non-bipartite.
  - I built B(H): 11,664 vertices, x ↦ x and x+5,832, edges (x, 5,832+x) and both orientations (a, 5,832+b),
    (b, 5,832+a) of each edge ab. apsp.c gives **"RESULT VALID d=13 D=5 n=11664"**: 13-regular, bipartite,
    diameter 5. That is 184 vertices more than the table's (13,5) = 11,480.
  - Scratch files: `/tmp/claude-0/-home-user-degree-diameter/2f50006c-2de8-5a85-afda-0208494f361a/scratchpad/dl124/`
    holds g124.edges, b135.edges and the compiled apsp. The coordinator should redo this from the URL.
  - No other cell gains from 2·N(Δ−1, D−1) with the current Comellas values. The only other hit is (13,9), and that
    comes from Comellas's (12,8) = 119,144,241, which is out of line with its neighbours ((11,8) = 9,739,368,
    (13,8) = 36,275,160, (12,9) = 178,084,211). It is probably a typo for 19,144,241, and doubling 19,144,241 does
    not beat 50,990,610. Do not use it without checking Comellas's (12,8) entry.

## Summary of what is confirmed from a primary source

| cells | construction source | status |
|---|---|---|
| (7,4), (11,4), (13,4), (15,4); (7,6), (11,6), (13,6), (15,6) | Delorme 1985 EJC §8(a),(b) doubling | read; q = 5 example in paper, others arithmetic |
| (16,4), (16,6) | same sets, tripling (§7, r = 2) with q = 13 | arithmetic matches exactly; not stated anywhere |
| (16,3) = 394 | ? (Delorme 1985 JGT or Bond–Delorme 1988?) | not found |
| (6,7) = 8,310, (8,7) = 40,586 | Delorme 1985 EJC §9 (edge insertion plus q−1 duplications), q = 5, 7 | read; formula in paper |
| other green D = 5, 7, 8 cells, (3,8), (3,10), (16,5) | DGQ "On large bipartite graphs" (unpublished) | not found; decodings inferred |
| (3,5) = 56 | Bar-Yehuda–Etzion 1992 (n = 28, F = (12,0,8,20)); also Bond–Delorme 1988 | BYE read and rebuilt |
| optimality of (3,5) | Jørgensen 1993; alternative proof Feria-Purón–Pineda-Villavicencio 2012 | secondary for Jørgensen; FPV read |
| (7,3) = 80, (4,5) = 160, (4,7) = 840, (3,7) = 168 | Hafner's adjacency lists (Bond–Delorme construction for 160 and 840; Conder for 168) | downloaded and checked |
| optimality of (7,3) | FMP 2013, Theorem 4.1 | read |
| (3,7) identity | C168.1 in Conder's census (1-arc-regular, \|Aut\| = 504, girth 12) | read; isomorphism to Hafner's file not tested |
| (11,3), (13,3), (15,3) | FMP 2013 Φ95 graphs; AL Theorem 1, order 2(q²+q+5) | read |
| all Loz cells | Loz thesis (restricted), metabelian preprint (missing) | not found; metacyclic order pattern inferred |
| (13,5) | 2·Mizuno (12,4) via B(H) = 11,664 | built and apsp-valid here; needs coordinator check |
