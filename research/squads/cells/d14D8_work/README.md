# d14D8_work: tools for the (14,8) cell (job cell-14-8, 2026-10-24)

The table value 14,172,480 (Delorme–Gómez–Quisquater, "On large bipartite graphs", credited on CombinatoricsWiki,
which still lists it) equals 40·|H(11)|: the incidence graph of the split Cayley hexagon H(11) (354,312 vertices,
degree 12) blown up 40 times with degree 12 + 2 = 14. All even-Δ D = 8 table values with Δ ≥ 10 fit
|V| = 5(q+5)/2 · |H(q)| with q = Δ − 3 (q = 7, 9, 11, 13), and (11,8) = 30·|H(8)|, (13,8) = 15·|H(11)| (Δ = q+2).

Build: `gcc -O2 -o hexgen ../../../p4/d6/hexgen.c && mkdir -p hex && ./hexgen 11` (writes hex/hex_q11.bin; q = p or p²,
p odd). `gcc -O3 -march=native -o lifteval lifteval.c` (and liftevalw.c, lifteval2.c).

- `hexlib.py`: load H(q) (points, lines, coordinates), write base graphs, BFS distances.
- `lifteval.c` (m ≤ 64) / `liftevalw.c` (m ≤ 1024): cyclic voltage lift of a bipartite base graph (points = side A,
  lines = side B), exact diameter test for even D by bitmask walks from (a, 0); `r:K:seed` samples K sources,
  `all` checks every source (exact, since Z_m translations are automorphisms).
- `lifteval2.c`: base graphs with loops / mixed lift colouring (star products H(q) * C_m).
- `mk_x0.py`, `mk_x1.py`, `mk_ratio.py`, `mk_star.py`: example designs (see each header).
