# (3,11) and (3,12): census graphs and our (3,11) record

**Ours: (3,11) n = 1,260** (6+6 voltage lifts over Z_105 and over C5 x (C7:C3), found by joint base+voltage
annealing; files research/squads/own-small/records/d3D11_n1260_*; |Aut| = 105). It beats the census value below.

## Known census graphs that exceed the lab's earlier new-cell values

The lab records (RESULTS.md, Oct 26 09:44 PT) list (3,11) 1,080 and (3,12) 1,320 as new cells. Published censuses
already contain larger bipartite cubic graphs with these diameters. They are not our constructions; credit the censuses.

| cell | n | graph | source | check |
|---|---:|---|---|---|
| (3,11) | 1,250 | CVT(1250,153), vertex-transitive | Potočnik–Spiga–Verret census of cubic vertex-transitive graphs (graphsym.net, Census3valentVT.zip) | cvt1250_153.check.txt |
| (3,11) | 1,200 | CAT(1200,1), arc-transitive | Foster census (fostercensus.graphsym.net, CubicETsparse6.zip) | cat1200_1.check.txt |
| (3,12) | 2,304 | CSS(2304,5), semisymmetric | Foster census | css2304_5.check.txt |

Each edge list was extracted with tools/cvt_get.py or tools/s6.py, checked with score48 and with the all-pairs checker
research/lifts/coordinator_check/apsp.c (valid at D, invalid at D - 1). The Foster census tables also list bipartite
graphs with diameter 13 on 3,360 vertices (CAT(3360,4)) and diameter 14 on 6,272 (CSS(6272,7)); the VT census stops at
1,280 vertices, so (3,12) and above are only covered there by the edge-transitive census.
