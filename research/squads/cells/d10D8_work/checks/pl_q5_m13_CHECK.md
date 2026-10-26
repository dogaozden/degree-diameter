# Check: Pluecker pencil design, q = 5, 13 copies (Delta = 8, diameter 8, 101,556 vertices)

Not a record (table (8,8) = 201,480); kept as the first structured, explained compound of copies of I(H(q)) at D = 8
that beats random lifts (random voltages reach 11-12 copies at q = 5). Builder: squad card r2_d8c/c6.

Build: `python3 research/squads/cells/d10D8_work/gen_pl.py 5 13 1 OUT neg` (needs hex/hex_q5.bin from `./hexgen2 5`).
The file is a Z_13 voltage lift for glift.c: points 0..3905, lines 3906..7811 of H(5); hexagon voltages 0; two
bijections sigma_1, sigma_2 mapping the points with pencil coordinate c(u) = [b(a,u) : b(a',u)] = kappa onto lines with
Pluecker pencil coordinate c'(L) = kappa (random inside classes), voltages f1 = 1 + c, f2 = -(1 + c).

Checks (2026-10-26, own-d8-compound):
- `glift OUT all`: COST 0 sources 7812 bad 0, degree 8, lift 101,556 vertices (the card ran it; re-run by Opus, the
  rebuild is byte-identical to the card's file).
- Explicit graph (each lift vertex (v, g) = v*13 + g, 406,224 edges): `gcheck EDGES 8 all`: GCOST 0, ecc_max 8.
- `apsp_mt EDGES 8 8 2` (coordinator checker, all-pairs BFS, no symmetry): n=101556 edges=406224 degree min=8 max=8
  bipartite=yes diameter=8, RESULT VALID d=8 D=8 n=101556.
- q = 7, m = 17 = 2q + 3 (same rule, axis seeds 1-12, 256 sampled sources each): COST 14-50, not valid.
