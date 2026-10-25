# research/d12D8/r2: round 2 of the cell-12-8 job (2026-10-25)

Main result: the (12,8) table value 4,650,100 comes from Gómez's ΩH₉ (PhD thesis 1986, §2.9.3), which has diameter 9.
See OMEGA_D9.md and research/squads/cells/d12D8.md. Valid (12,8) Haar graphs are in ../haar/ and research/frontier/sols/.

Build: `gcc -O3 -march=native -fopenmp -o X X.c` for each .c file; apsp is research/lifts/coordinator_check/apsp.c.
Hexagon files and edge colourings live in ../hex/ (not committed): `../tools/hexgen q` (run in research/d12D8/, writes
hex/hex_q{q}.bin) and `python3 colour.py q 1` (writes hex/col_q{q}_s1.npy).

| file | what |
|---|---|
| mk_omega.py | Gómez's ΩB₁ for B₁ = H(q) incidence graph, as read from Figs 2.21a/b; writes an edge list for apsp / eccs |
| eccs.c | eccentricity and distance counts from given sources (edge-list graphs of any size that fit in memory) |
| ecc.py | per-class eccentricities (new vertex / copy vertex) for small ΩB₁ |
| colour.py | proper (q+1)-edge-colouring of H(q) by repeated perfect matchings (scipy) |
| classcheck.c | scan structured voltage families: base edges carry a class, a parameter file assigns Z_a × Z_b voltages per class |
| mk_cls.py, mk_pair.py | class base / "pair design" (colour pairs as oriented 2-factors) for H(q) + 2 hops |
| gencheck.c | diameter check of an affine permutation lift of a general (non-bipartite) base graph, loops allowed |
| mk_gstar.py | Delorme's general product G ∗ C_m (Eur. J. Combin. 6 (1985) §4) for G = H(q) incidence graph |
| mk_bdouble.py | explicit edge list of a gencheck-format product, or of its bipartite double |
| mk_star.py, mk_dstar.py, mk_dstar2.py | bipartite affine "star product" attempts on H(q) (all fail: see the cell report) |

Commands behind the claims:
- `python3 mk_omega.py 3 aab om3.txt && ./apsp om3.txt 6 9` → diameter 9 (14,560 vertices); `python3 ecc.py om3.txt 15 728`
- `python3 mk_omega.py 5 abab om5.txt && ./apsp om5.txt 8 9` → diameter 9 (195,300 vertices, 47 s)
- `python3 mk_omega.py 9 aaabbb om9.txt && ./eccs om9.txt 3985800 0` → eccentricity 9 from a new vertex (1,062,882 at
  distance 9) and from a copy vertex (177,147 at distance 9); 4,650,100 vertices, 27.9M edges, ~1 min to write.
- `python3 mk_gstar.py 3 19 7 g.gen && ./gencheck g.gen 8 7 1` → 0 unreached (G ∗ C₁₉ has diameter 8 at q = 3)
