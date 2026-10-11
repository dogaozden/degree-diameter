# Candidate new records (bipartite degree-diameter)

Status: **verified graphs, literature check pending.** Not yet claimed as records.

Reference table: Combinatorics Wiki, "The Degree Diameter Problem for Bipartite Graphs"
(http://combinatoricswiki.org/wiki/The_Degree_Diameter_Problem_for_Bipartite_Graphs), table "as of January 2012",
page last edited 2022.

## Best graph per case

| (Δ, D) | table record | ours | upper bound | graph | found by | file |
|---|---|---|---|---|---|---|
| (4, 5) | 160 | **162** | 236 | 4-regular, 81 + 81 | C island c-d4d5, g002-c08 | d4D5/162-c-d4d5-g002-c08.json |
| (5, 5) | 336 | **344** | 676 | 5-regular, 172 + 172, 860 edges | C island c-d5d5, g003-c05 | d5D5/344-c-d5d5-g003-c05.json |
| (7, 4) | 346 | **356** | 518 | degrees 6–7, 174 + 182, 1218 edges | Python island spec-d7d4, g004-c23 | d7D4/356-spec-d7d4-g004-c23.json |
| (11, 3) | 190 | **192** | 220 | 11-regular, 96 + 96 | C island c-d3fam, g001-c00 | d11D3/192-c-d3fam-g001-c00.json |
| (11, 4) | 1734 | **1773** | 2222 | degrees 10–11, 871 + 902, 9530 edges | Python island spec-d11d4, g004-c01 | d11D4/1773-spec-d11d4-g004-c01.json |

Upper bounds are the wiki's "lowest known upper bounds" table. Every graph sits below its bound.

Other verified graphs that beat the table, kept as independent confirmations:

| (Δ, D) | ours | graph | found by | file |
|---|---|---|---|---|
| (4, 5) | 162 | 4-regular, 81 + 81, 324 edges | Python island spec-d4d5, g005-c05 | d4D5/162-spec-d4d5-g005-c05.json |
| (7, 4) | 354 | degrees 6–7, 172 + 182, 1204 edges | C island c-d7d4, g002-c13 | d7D4/354-c-d7d4-g002-c13.json |
| (7, 4) | 349 | degrees 6–7, 172 + 177, 1204 edges | Python island spec-d7d4, g003-c13 | d7D4/349-spec-d7d4-g003-c13.json |

## Verification (2026-10-10, on the Mac)

1. All eight graphs pass `scripts/verify_record.py`: the trusted checker, the networkx checker, and a
   from-scratch check (adjacency sets, explicit 2-colouring, BFS from every vertex for the exact diameter).
   For 1773, the from-scratch check ran 1773 searches (33.8 million edge steps) and every vertex has
   eccentricity exactly 4. All three checkers also reject two sabotaged copies of that graph
   (a pendant vertex, which makes the diameter 5, and one extra edge inside a side, which makes an odd cycle).
2. Each generating program (saved next to its graph as `*.program.py`) was re-run fresh on a different
   machine than the cloud island that found it, with seed 0 and a 60 s limit, and rebuilt the same order:
   162, 162, 344, 349, 354, 356, 192, 1773.

Re-run the check: `python scripts/verify_record.py records/bipartite_dd/d11D4/1773-spec-d11d4-g004-c01.json 11 4`

## Where the old records come from

Who holds each beaten entry, from the wiki table's colour key:

| (Δ, D) | old value | found by |
|---|---|---|
| (4, 5) | 160 | Paul Hafner, and independently Eyal Loz (the wiki cites no paper) |
| (5, 5) | 336 | Eyal Loz, in the project "The degree/diameter problem for several classes of graphs" (Loz, Pérez-Rosés, Pineda-Villavicencio) |
| (7, 4) | 346 | a graph duplication by Delorme and Farhi |
| (11, 3) | 190 | Feria-Purón, Miller and Pineda-Villavicencio, and independently Araujo-Pardo and López |
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
