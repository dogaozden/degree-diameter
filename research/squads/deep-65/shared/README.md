# deep-65 shared tools (Haiku workers: copy into your folder, do not edit here)

Build: `gcc -O3 -march=native -o X X.c -lm`. GAP is installed (`gap -q`); group tables: 
`gap -q -c 'ORDER:=258; OUTDIR:="groups";' ../../tools/gap_tables.g` writes groups/sg_258_i.txt (m, then the m x m
multiplication table, element 0 = identity).

| file | what |
|---|---|
| score65.c | `score65 EDGES`: n, degrees, bipartite, bad = unordered pairs at distance > 5 (the scorer) |
| apsp.c | coordinator checker: `apsp EDGES 6 5` must print RESULT VALID (and `apsp EDGES 6 4` INVALID) |
| mcos.c | annealer for multi-orbit coset graphs (header explains TYPE, N, CLS, SECS, SEED, EDGES) |
| t18.c | tabu for type "1,k|1,k" (header explains usage) |
| ../tools/hubk.c | Opus's exact search + algebraic cost for "Haar degree 5 + hubs of size k + hub graph of degree 6-k" |
| h684.edges | the 684 record graph (Haar graph of SmallGroup(342,12)); vertices 0..341 side A, 342..683 side B |
| damage684.c | `damage EDGES`: for each edge at vertex 0, the pairs that become far when it is deleted |
| cost2_294_11.edges | the 686-vertex hub graph with bad = 294 (exactly 2 missing elements, proven optimal in its family) |
| tabu.c, kopt.c | lift tools (vl format): `tabu SOL GROUP [OUT]` (env SECS, SEED, INIT=random), `kopt SOL GROUP K` (exact K-change neighbourhood) |
| lift_294_11_cost12.vl, lift_147_3_cost12.vl | the two bad-294 graphs at 686 as lifts of 14-vertex bases by C7 x C7 (tables c7xc7_from_*.grp); lift cost 12 |
