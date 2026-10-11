# Candidate new records (bipartite degree-diameter)

Status: **verified graphs; the literature check (2026-10-10) found nothing larger and no bound below them.**
Not yet reported to the table's moderators.

Reference table: Combinatorics Wiki, "The Degree Diameter Problem for Bipartite Graphs"
(http://combinatoricswiki.org/wiki/The_Degree_Diameter_Problem_for_Bipartite_Graphs), table "as of January 2012",
page last edited 2022.

## Best graph per case

| (Δ, D) | table record | ours | upper bound | graph | found by | file |
|---|---|---|---|---|---|---|
| (4, 5) | 160 | **162** | 236 | 4-regular, 81 + 81 | C island c-d4d5, g002-c08 | d4D5/162-c-d4d5-g002-c08.json |
| (5, 5) | 336 | **352** | 676 | 5-regular, 176 + 176, 880 edges | C island c-d5d5, g010-c30 | d5D5/352-c-d5d5-g010-c30.json |
| (7, 4) | 346 | **359** | 518 | degrees 6–7, 177 + 182, 1239 edges | Python island spec-d7d4, g017-c11 | d7D4/359-spec-d7d4-g017-c11.json |
| (11, 3) | 190 | **192** | 220 | 11-regular, 96 + 96 | C island c-d3fam, g001-c00 | d11D3/192-c-d3fam-g001-c00.json |
| (13, 3) | 274 | **276** | 314 | 13-regular, 138 + 138, 1794 edges | C island c-d3fam, g003-c19 | d13D3/276-c-d3fam-g003-c19.json |
| (7, 5) | 1134 | **1140** | 3106 | 7-regular, 570 + 570, 3990 edges | Python island spec-d7d5, g016-c15 | d7D5/1140-spec-d7d5-g016-c15.json |
| (15, 3) | 374 | **376** | 422 | 15-regular, 188 + 188, 2820 edges | C island c-d3fam-w2, g002-c12 | d15D3/376-c-d3fam-w2-g002-c12.json |
| (11, 4) | 1734 | **1774** | 2222 | degrees 10–11, 872 + 902, 9541 edges | Python island spec-d11d4, g010-c19 | d11D4/1774-spec-d11d4-g010-c19.json |

Upper bounds are the wiki's "lowest known upper bounds" table. Every graph sits below its bound.

Other verified graphs that beat the table, kept as independent confirmations:

| (Δ, D) | ours | graph | found by | file |
|---|---|---|---|---|
| (4, 5) | 162 | 4-regular, 81 + 81, 324 edges | Python island spec-d4d5, g005-c05 | d4D5/162-spec-d4d5-g005-c05.json |
| (5, 5) | 344 | 5-regular, 172 + 172, 860 edges | C island c-d5d5, g003-c05 | d5D5/344-c-d5d5-g003-c05.json |
| (7, 4) | 358 | degrees 6–7, 176 + 182, 1232 edges | Python island spec-d7d4, g008-c11 | d7D4/358-spec-d7d4-g008-c11.json |
| (7, 4) | 356 | degrees 6–7, 174 + 182, 1218 edges | Python island spec-d7d4, g004-c23 | d7D4/356-spec-d7d4-g004-c23.json |
| (11, 4) | 1773 | degrees 10–11, 871 + 902, 9530 edges | Python island spec-d11d4, g004-c01 | d11D4/1773-spec-d11d4-g004-c01.json |
| (7, 4) | 354 | degrees 6–7, 172 + 182, 1204 edges | C island c-d7d4, g002-c13 | d7D4/354-c-d7d4-g002-c13.json |
| (7, 4) | 349 | degrees 6–7, 172 + 177, 1204 edges | Python island spec-d7d4, g003-c13 | d7D4/349-spec-d7d4-g003-c13.json |

## Verification (2026-10-10, on the Mac)

1. All fifteen graphs pass `scripts/verify_record.py`: the trusted checker, the networkx checker, and a
   from-scratch check (adjacency sets, explicit 2-colouring, BFS from every vertex for the exact diameter).
   For the first 1773 graph, the from-scratch check ran 1773 searches (33.8 million edge steps) and every vertex has
   eccentricity exactly 4. All three checkers also reject two sabotaged copies of that graph
   (a pendant vertex, which makes the diameter 5, and one extra edge inside a side, which makes an odd cycle).
2. Each generating program (saved next to its graph as `*.program.py`) was re-run fresh on a different
   machine than the cloud island that found it, with seed 0 and a 60 s limit. Fourteen rebuilt the same order:
   162, 162, 344, 352, 349, 354, 356, 358, 359, 192, 276, 376, 1140, 1773. Where the island saved its own copy, five rebuilds are
   edge-for-edge identical to it (162, 192, 276, 344, 352, 356, 376, 1140); 358 and the first 1773 have the same order with
   different edges, because those searches run to a clock deadline and depend on the machine.
3. The 1774 program rebuilt only 1773 on the Mac, every time, with time limits from 12 s to 120 s. The 1774
   graph here is the island's own saved copy (from its branch `spec-d11d4`), checked as in step 1.

Re-run the check: `python scripts/verify_record.py records/bipartite_dd/d11D4/1773-spec-d11d4-g004-c01.json 11 4`

## Where the old records come from

Who holds each beaten entry, from the wiki table's colour key:

| (Δ, D) | old value | found by |
|---|---|---|
| (4, 5) | 160 | Paul Hafner, and independently Eyal Loz (the wiki cites no paper) |
| (5, 5) | 336 | Eyal Loz, in the project "The degree/diameter problem for several classes of graphs" (Loz, Pérez-Rosés, Pineda-Villavicencio) |
| (7, 4) | 346 | a graph duplication by Delorme and Farhi |
| (11, 3) | 190 | Feria-Purón, Miller and Pineda-Villavicencio, and independently Araujo-Pardo and López |
| (13, 3) | 274 | Araujo-Pardo and López (2022) |
| (7, 5) | 1134 | Eyal Loz's computer-search project (Loz, Pérez-Rosés, Pineda-Villavicencio) |
| (15, 3) | 374 | Araujo-Pardo and López (2022) |
| (11, 4) | 1734 | a graph duplication by Delorme and Farhi |

Sources:

- C. Delorme, G. Farhi, "Large graphs with given degree and diameter, Part I", IEEE Trans. Computers C-33 (1984) 857–860. doi:10.1109/TC.1984.1676504
- C. Delorme, "Large bipartite graphs with given degree and diameter", J. Graph Theory 9 (1985) 325–334. doi:10.1002/jgt.3190090304 (the wiki gives volume 8)
- E. Loz, G. Pineda-Villavicencio, "New benchmarks for large-scale networks with given maximum degree and diameter", The Computer Journal 53 (2010) 1092–1105. doi:10.1093/comjnl/bxp091
- R. Feria-Purón, M. Miller, G. Pineda-Villavicencio, "On large bipartite graphs of diameter 3", Discrete Math. (2013). doi:10.1016/j.disc.2012.11.013, arXiv:1203.3588
- G. Araujo-Pardo, N. López, "On new record graphs close to bipartite Moore graphs", Graphs and Combinatorics (2022). doi:10.1007/s00373-022-02500-3, arXiv:2005.02427
- M. Miller, J. Širáň, "Moore graphs and beyond: a survey of the degree/diameter problem", Electron. J. Combin., Dynamic Survey DS14 (2nd ed. 2013). doi:10.37236/35

Upper bounds (bipartite graphs close to the Moore bound):

- C. Delorme, L. Jørgensen, M. Miller, G. Pineda-Villavicencio, "On bipartite graphs of diameter 3 and defect 2", J. Graph Theory 61 (2009) 271–288. doi:10.1002/jgt.20378
- C. Delorme, L. Jørgensen, M. Miller, G. Pineda-Villavicencio, "On bipartite graphs of defect 2", European J. Combin. 30 (2009) 798–808. doi:10.1016/j.ejc.2008.09.030
- G. Pineda-Villavicencio, "Non-existence of bipartite graphs of diameter at least 4 and defect 2", J. Algebraic Combin. 34 (2011) 163–182. doi:10.1007/s10801-010-0266-0
- R. Feria-Purón, G. Pineda-Villavicencio, "On bipartite graphs of defect at most 4", Discrete Appl. Math. 160 (2012) 140–154. doi:10.1016/j.dam.2011.09.002

Nearby recent work (not on the bipartite table):

- F. Comellas, "Table of large graphs with given degree and diameter", arXiv:2406.18994 (2024). Updates the general table since 2013.
- R. Mizuno, "New lower bounds for the degree/diameter problem via interaction with a browser-accessible LLM", arXiv:2606.15860 (June 2026). General graphs, found with an LLM.

## Literature check (2026-10-10)

A separate agent searched arXiv (through 11 Oct 2026), OpenAlex, Crossref (EJC, Discrete Math, JGT, DAM),
Google Scholar and Semantic Scholar citations, the wiki's edit history, and the pages of Loz, Exoo, Comellas
and Pineda-Villavicencio.

- **All seven cases:** no published value above the table, and no proven upper bound below our graphs.
  (7,5) was checked separately after 1140 was found: 1134 is unchanged since 2012 and no paper gives a
  (7,5) value.
- **The wiki:** the cells for (4,5), (5,5), (7,4), (11,3) and (11,4) are unchanged since its first revision
  (17 Jan 2012). (13,3) went from 270 to 274 on 30 Mar 2021 (Araujo-Pardo and López). The upper-bound table
  is unchanged since 2012. The survey (Miller and Širáň, 2013) and Loz's 2009 table agree.
- **Upper bounds:**
  - (4,5) 236 and (5,5) 676 are the Moore bound minus 6 (Feria-Purón and Pineda-Villavicencio, Prop. 6.4).
  - (7,4) 518 and (11,4) 2222 are the Moore bound itself. Reaching it would need a generalized quadrangle
    of order 6 or 10, which nobody has ruled out.
  - (11,3) 220 is the Moore bound minus 2.
  - (7,5): the wiki shows 3106 but colours it "Moore bound minus 6", which is 3104 (Moore bound 3110);
    Prop. 6.4 of Feria-Purón and Pineda-Villavicencio gives 3104.
  - (13,3) 314 is the Moore bound. Reaching it would need a projective plane of order 12, which is open.
- **Araujo-Pardo and López's family** gives 2(q² + q + 5) vertices at degree q + 2: 190 at q = 9 and 274 at
  q = 11. Our 192, 276 and 376 are each exactly 2 more (374 is q = 13). Their paper's Problem 3 asks readers to "improve our
  construction".
- **Not a Haar graph:** Haanpää (2004) shows abelian Haar graphs of degree 11 and diameter 3 stop at 190.
  Our 192 is not one; its program grows the Araujo-Pardo–López 190 graph by two vertices.
- **Could not read:** Feria-Purón's PhD thesis (bot-blocked; it claims improved upper bounds) and
  Araujo-Pardo's 2025–26 book chapter on bipartite biregular graphs (paywalled). An upper bound below one of
  our verified graphs would be a mistake, so the only open risk is a larger graph in those two sources.

Reporting: the wiki takes no anonymous edits; changes go through a moderator. The degree/diameter
moderators are Eyal Loz (chief), Hebert Pérez-Rosés and Guillermo Pineda-Villavicencio, and Nacho López is
named as a maintainer. Araujo-Pardo and López are the natural people to tell about (11,3) and (13,3).

## Why +2 works for (11,3), (13,3) and (15,3)

The three +2 graphs add a fourth "hat" pair to the Araujo-Pardo–López construction, with a small rotation of
three incidences to make room. The clean rule works in every projective plane of order q ≥ 4 and gives
2(q² + q + 6) vertices at degree q + 2 and diameter 3. A proof, computer checks and SAT evidence against +3 and +4
inside the same family are in `research/plus2/REPORT.md`. The proof was written by a model and checked by computer;
it still needs a mathematician's reading.
