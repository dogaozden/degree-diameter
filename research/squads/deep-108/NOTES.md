# deep-108: working notes (Opus-led depth run on Δ10·D8, table 1,176,480)

Started 2026-11-01 22:39 UTC, branch claude/d10-d8-depth-search-3b5yyu. Leads from handsoff-108: (a) energy-3 Haar
orbit states on PSL(2,23) x Z97, (b) coset family K (PSL(2,229), H = D5, one regular double coset, exhaustive min 4).

## cq: orbit-quotient evaluator for bi-coset graphs (cq/cq.c, cq2.c with a Z_m factor, cq3.c for A x PSL(2,p))
X(G; L, R; D): A = cosets Lx, B = cosets Ry, Lx ~ Ry iff x y^-1 in D (D = union of L z R). The A-root BFS is invariant
under right multiplication by L, so it runs on L-orbits (double cosets) with a bottom-up last level: 17 ms per A-root BFS
on K against 130 ms for handsoff's exh.c. Validated: 200/200 random K classes identical to c6b's K_scanA.tsv;
class 4233 gives uBA 4, uAA 0, uBB 0. cq2 with m = 1 and cq3 with trivial first factor reproduce the same K values.

## (b) Why K's minimum is 4
- Census of the L-orbits on B-cosets for K: 1 orbit of size 1, 11 of size 2 (stabiliser C5: cosets in N(C5) = D230),
  113 of size 5 (stabiliser C2), 59,985 regular. An orbit of size s is hit by about lambda*s/10 independent walk-orbits,
  lambda = W/N = 8.96, so P(miss) = e^(-lambda s/10): 0.41, 0.167, 0.011, 1.3e-4. Expected special misses
  0.41 + 1.83 + 1.28 = 3.5, i.e. P(all special orbits covered) is about 3 % even when every regular orbit is covered.
- Class 4233: the 4 uncovered B-vertices are exactly two of the 11 size-2 orbits (stabiliser C5). All 59,985 regular
  orbits and all 113 size-5 orbits are covered. The two missing classes are normaliser cosets of C5.
- Median members: 30-34 regular orbits uncovered (Poisson orbit model: 7.7) plus 4-5 size-2 and 4-5 size-5 orbits.
  The tax (4.4x) is in the regular orbits. Level counts are tree-like up to level 4 and the level-5 loss (4.5-7 %) is
  close to birthday collisions on 60k orbits, so it is not short cycles. corr mode: among B-orbits beyond distance 5,
  the number k of neighbours at distance 6 is overdispersed against Binomial(10, f6): k = 0 occurs 31 times against
  4.7 expected, k = 1 178 vs 73, k = 2 987 vs 505 (median member). Coverage of the 10 neighbours of a vertex is
  positively correlated; that is the tax.
