# (15,7): 7 copies of H(11) plus hubs (cell-15-7 job, 2026-10-24)

Table value 2,480,184 = 7·|H(11)| (2k+1 copies of the generalized hexagon H(q), Δ = q+1+k, here q = 11, k = 3).

Construction (`kcopy_hub.c`): copies c ∈ Z_7 of the incidence graph of H(11); cross edges (p,c) ~ (M(p), c+j), j = 1,2,3,
for one bijection M: points → lines (all three bijections equal). Freed flags (p_a, l_a = M(p_a)): p_a loses its 21
cross edges; 3 line-side hubs on the column {(p_a,c)} and 3 point-side hubs on the column {(l_a,c)}: +6 vertices per
freed flag. M near the freed flags comes from the exp2-squad hub search (`d7hex.c`, copied) with a new
region-matched cover installation (`d7hexr.c`, alg 4). The same M gives the 3-copy (13,7) and 5-copy (14,7) versions.

Why only freed sources and hubs need checking: see the header of `kcopy_hub.c`.

Rebuild: `gcc -O2 -o hexgen ../p4/d6/hexgen.c && ./hexgen 11` (writes hex/hex_q11.bin, 4 s), then
`gcc -O3 -fopenmp -o kcopy_hub kcopy_hub.c && ./kcopy_hub check hex/hex_q11.bin SOL 3`
(`full` for the symmetric all-sources check, `edges` for apsp.c input).
