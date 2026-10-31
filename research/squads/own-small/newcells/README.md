# (3,11) and (3,12): census graphs and our records

**Ours: (3,11) n = 1,320**: a 4+4 voltage lift over C3 x (Z11:Z5) = SmallGroup(165,1) (squad round 3, card x6,
through the director's queue; records/d3D11_n1320_*, explicit coordinates d3D11_n1320_c3xf55.txt and builder
build_d3D11_n1320.py). Earlier the same day: n = 1,260, 6+6 lifts over Z_105 and over C5 x (C7:C3)
(records/d3D11_n1260_*). Both beat the census value below.

**Ours: (3,12) n = 2,368**: a 4+4 voltage lift over Z37 x|_6 Z8 = SmallGroup(296,3) (joint annealing to cost 2, then
the exact two-move search tools/polish.c; records/d3D12_n2368_*, builder build_meta_lift.py SOL 37 8 6 OUT). It beats
CSS(2304,5) below. Checked with score48 and apsp.c (valid at D = 12, invalid at D = 11), also on the independent rebuild. All found by joint base+voltage annealing (salift_s, D = 11)
and checked with score48 and apsp.c (valid at D = 11, invalid at D = 10).

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
