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
- Tests of the tax mechanism (cq modes fiber, disp, quad; two median members and class 4233):
  - N(C5) = D230 fibres (23 B-vertices each): apart from the special fibre, uncovered vertices lie 310-340 alone and
    20-25 in pairs (independent: about 3 pairs). Some clustering, but not the bulk.
  - Displacement m(v) = min over g in Stab(v), g != e, of d(H, Hg): about 520 regular B-orbits per member have m = 2;
    they are uncovered at 3.8-5.9 per 1000 against 0.55-0.62 for m = 6 (7-10x), but contribute only 2-3 of ~30
    uncovered orbits. These are exactly the orbits with 4-cycles in the orbit quotient (4 repeated second neighbours).
  - 96 % of B-orbits have no repeated second neighbour in the quotient, and most uncovered orbits are among them.
  - So the remaining 4x excess is not local (tree-like to radius 4 in the graph, radius 2 in the quotient); it is a
    global correlation that random-graph models do not have. Haar graphs on random S pay about 1.5x.
- Lead (a), fixed-letter swap (leadA/f0test.sh): the energy-3 state (g4a) with e replaced by each of the 11 other
  alpha-fixed letters (F0 = 1..11) costs 42-157 (base 3). About half of all words contain the fixed letter, so the
  swap is close to a random restart. Dead.

## (b) generalised: all h = 10 one-double-coset families near the bound
- Isomorphism classes (cq `classes`): D -> a D b^-1 for a in N_G(L), b in N_G(R) is an isomorphism (Lx -> Lax,
  Ry -> Rby), besides conjugation by N_PGL(L) cap N_PGL(R) and D -> D^-1 when L = R. Class counts (upper bounds on
  distinct graphs): K 16,293 (as exh.c); C = PGL(2,181) (D5n, D5n) 8,226 (handsoff counted 16,407: it missed a != b);
  PGL(2,181) (C10, D5n) 873; (D5s, D5n) 14,832. (C10,C10), (D5s,D5s), (C10,D5s) are disconnected (L, zRz^-1 in PSL).
- Exhaustive scans (scans/, 59,292 members each, A-root all, B-root for uBA+uAA <= 200):
  (C10, D5n): exact min 64 (uBB 0), median 364, best 8 class minima 64 76 88 96 102 102 103 109. E_s = 2.9.
  (D5s, D5n): exact min 44 (uBB 0), median 350, best 8 class minima 44 44 52 54 54 54 56 56. E_s = 2.9.
  Both dead. K's 4 (next 33) is an outlier among about 40k distinct h = 10 graphs in PSL/PGL(2,q).
