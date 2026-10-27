# c12: large-alpha torus families in PSL(2,q), Delta ~ q

gen_torus.py q split|nonsplit norb seed: S = {I} u union of norb orbits {T^i x T^-i}, x random generic per orbit
(det 1, b,c != 0). Split T = diag(g,1/g), order (q-1)/2 in PSL; nonsplit T = companion matrix of x^2-sx+1 with PSL
order (q+1)/2. Checked with haar_ecc psl q 1. Grid: results.tsv (run_grid.py), primes 29..61, seeds 1-4.

Findings (q >= 31):
- No family has diameter <= 4 (no flag). Diameter 4 is impossible for one orbit at large q by counting:
  |G| ~ q^3/2 > Delta(1+(Delta-1)^2) ~ q^3/8.
- 1 orbit: diam 6-7. 2 orbits: diam 5-6. 3 orbits: diam 5 for every q >= 31 (split and nonsplit).
- Ratio |G|/W(Delta,diam) is maximal at q = 31 (it falls with q since W ~ Delta^(diam-1)).
- Best: split torus, 2 orbits, seed 3, q=31: Delta=31, diam 5, |G|=14880, W=837931, ratio 0.0178.
- Some single-orbit seeds are disconnected at small q (q=5,7,11); excluded from scoring.
