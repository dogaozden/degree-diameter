# (16,5) bipartite graphs from job beat-16-5 (route-chart lifts, not Haar graphs)

| file | vertices | how to rebuild (run here) | check file |
|---|---|---|---|
| d16D5_n36864_rcl_pv_c3a4.edges.gz | **36,864** | `python3 ../beat165/rcl/buildlift_pvv.py ../beat165/rcl/g36_11_table.txt ../beat165/rcl/ctrl_k2_m36_1.txt ../beat165/rcl/vchart_k2_m36_1.txt OUT.edges` (sha256 0440a2606d9ffc8ae6303bea70be9c1d15ba600d9e38a7cd88b80148915c50ec uncompressed) | `../beat165/check_d16D5_36864.txt` |
| d16D5_n33792_rcl_pv_c22.edges.gz | 33,792 | `python3 ../beat165/rcl/buildlift_pvv.py ../beat165/rcl/g22_2_table.txt ../beat165/rcl/ctrl_k3_m22_2.txt ../beat165/rcl/vchart_k3_m22_2.txt OUT.edges` (sha256 e8b0933f6b2facc98437065cc820534240dbe6c14ca68d298578c7234f76d0ce) | `../beat165/check_d16D5_33792.txt` |
| d16D5_n32768_rcl_g64_43.edges.gz | 32,768 | `python3 ../beat165/rcl/buildlift.py ../beat165/rcl/g64_43_table.txt 0 1 2 29 ../beat165/rcl/chart_g64_43.txt OUT.edges` (sha256 18fb910749f631fd6adcf883578c043125344c70fd9ba68548e85d2b98049a26) | `../beat165/check_d16D5_32768.txt` |

All three are 16-regular, bipartite and of diameter 5 by `apsp OUT.edges 16 5` (research/lifts/coordinator_check/apsp.c,
all pairs, no symmetry assumed); with D = 4 they fail. Each was also rebuilt independently in GAP from the
definition, using GAP's own group elements and GF(4) arithmetic: `../beat165/rcl/rebuild_gap.g` (32,768) and
`../beat165/rcl/rebuild_pvv_gap.g` with the parameter files `rebuild_pvv_33792.g` and `rebuild_pvv_36864.g`. In each case
the sorted edge list is identical to the saved one.

Format: the first line is the number of vertices n, then one edge "u v" per line. Side A is ids < n/2. Vertex
(c, x) of the lift is c·256 + x₁ + 4x₂ + 16x₃ + 64x₄, where c is the controller vertex and x ∈ F₄⁴ is coded
0, 1, 2, 3 = 0, 1, ω, ω².

Construction: see `../BEAT_16_5.md` §4 (lemma §4.1, the 36,864 graph §4.9). The controller is a 4-regular bipartite
graph of diameter 5 with a 4-cycle at every vertex. For the 36,864 graph it has 72+72 vertices: 2+2 base vertices
lifted by SmallGroup(36,11) = C₃ × A₄. Each controller edge u → σ_t(u) lifts to the 4 edges
(u, x) ~ (σ_t(u), A x + λ b), λ ∈ F₄, with (A, b) chosen per base vertex and label.
