# (10,5) ≥ 4,820: DM lift of W(7) with 5 freed flags, 20 hubs and a hub graph

Base: the doubled-matching Z6-lift of W(7) (research/d10D7/DM_D5.md; 4,800 vertices). Freed flags (p_i, l_i = sigma(p_i)),
p_i on l_i, for p = 28, 46, 86, 128, 220: the 12 lift edges of each p_i's doubled matching edge are deleted; two hubs are
joined to the fibre (p_i, 0..5) and two to the fibre (l_i, 0..5) (+4 vertices per flag). Same-side hubs of
non-collinear freed points (non-concurrent freed lines) get a common neighbour through 38 hub-hub edges (line-side hub
to point-side hub, at most 4 per hub). sigma was chosen by a perfect matching (flaggreedy.py) so that every freed
flag has "exact coverage" (sigma maps the 49 points collinear with p_i off l_i onto lines meeting l_i, and the 49 lines
meeting l_i not through p_i come from points collinear with p_i), then nu and sigma (structure-preserving swaps) were
annealed for the coset-0 condition with dmfast_hub.c. 4,820 vertices, 24,098 edges, max degree 10.

Files: `graphs/d10D5_n4820_gqdm_flags5.sol` (dmhub format; line `hubgraph` lists hub-graph edges as pairs (a, b):
line-side hub a = i*H + s joined to point-side hub b = j*H + t), `graphs/d10D5_n4820_gqdm_flags5.edges.gz`.

Rebuild and check (from research/squads/d10D5/hubs):
    gcc -O2 -o gqgen ../../../d10D7/gqgen.c && mkdir -p gq && ./gqgen 7
    python3 build_hub.py gq/gq_q7.bin graphs/d10D5_n4820_gqdm_flags5.sol x.edges
    gcc -O3 -o apsp ../../../lifts/coordinator_check/apsp.c && ./apsp x.edges 10 5

Result (2026-10-25, cloud session): `n=4820 edges=24098 degree min=9 max=10 bipartite=yes diameter=5`,
`RESULT VALID d=10 D=5 n=4820`; with D=4 `RESULT INVALID` (diameter exactly 5).
sha256 of the edge list (build_hub.py and dmhub.c write the same file):
17376761099bc16858c9f4f472e52ea29943387957492b5c7f05f9f5ee8d2169
