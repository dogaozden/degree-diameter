# Diameter-8 lifts of the generalized hexagon: notes

bigcheck-dist lead, 2026-10-25. Tools in this folder; checker ../bcd.c.

## 1. Target cells

At D = 8 the table has, for Δ = q+3, exactly 5·⌊(q+5)/2⌋ copies of the incidence graph of H(q)
(|H(q)| = 2(q+1)(q⁴+q²+1)):

| (Δ,8) | q | table | copies | our Haar record |
|---|---|---:|---:|---:|
| (10,8) | 7 | 1,176,480 | 30 | none (Haar orbit search reached cost 12, STRUCTURE.md §7) |
| (11,8) | 8 | 2,246,940 | 30 | 2,258,520 |
| (12,8) | 9 | 4,650,100 | 35 | none (above the Haar first-moment ceiling) |
| (14,8) | 11 | 14,172,480 | 40 | none (above the ceiling) |
| (16,8) | 13 | 36,201,060 | 45 | none (above the ceiling) |

and (13,8) = 5,314,680 = 15·|H(11)| at Δ = q+2 (our Haar record 6,999,552 beats it). The survey credits Delorme 1985;
we do not have his definition.

## 2. The family searched: cyclic lifts of H(q) plus r bijections

Base B: incidence graph of H(q) (points P, lines L, |P| = |L| = N) plus r bijections σ_j : P → L, edge p — σ_j(p).
Δ = q+1+r. Lift over Z_M: voltage on every base edge, lift vertices (x, g). Size M·|H(q)|. Symmetry: the Singer torus τ
of SL(3,q) ⊂ G2(q) (x ↦ Mx on (X0,X1,X2), y ↦ M^{-T} y on (X4,X5,X6)), of order q²+q+1 (divided by 3 when 3 | q−1)
acts freely on points and lines (singer.py); with τ-equivariant σ_j and τ-invariant voltages the lift needs one BFS
source per τ-orbit (252 at q = 5, 2064 at q = 7). The Z_5-copy product of the D = 7 table graph X_2 is the special
case "voltages ≡ 0 (incidence), 1, 2 (σ_1, σ_2) mod 5".

**Computation (Δ = q+3, D = 8).** Cost = pairs (source, vertex) at distance > 8.

| q | M | random τ-invariant voltages | best after annealing / search |
|---|---|---:|---|
| 5 | 16 | ~8 | 0 (valid) |
| 5 | 17 | | 0: squad c7, random sampling; bcd VALID, n = 132,804 |
| 5 | 20 | ~70 | 2 (x2s) |
| 5 | 25 | ~1,270 | ~580 (x2s), Delorme: 25 |
| 5 | 31 | ~7,800 | (31 would beat our (8,8) record) |
| 7 | 20 / 24 / 28 / 31 | 1,038 / 10,590 / 62,710 / 177,758 | Delorme: 30 |

So search over voltages reaches about 80 % of Delorme's copy count at q = 5 and less at q = 7. Random-like lifts of
any base are no better than Haar graphs (same walk counts, more sources); the hexagon helps only with structure.

Where annealed solutions fail: point-line pairs at base distance 1, 3, 5 (mostly 5). Reduced walks of length ≤ 7
between such pairs number 155-220 (min over pairs, q = 5, 7), so counting does not forbid M ≈ 30-40. In the
Z_5 × Z_k product family, pairs at distance 1 and 3 have only 11-16 walks in their Z_5 class, which caps k at
about 11 (Delorme's k = ⌊(q+5)/2⌋ = 6 at q = 7).

## 3. Routes (one jump at each end) and a provable family

Take incidence voltages 0 and copy shifts f_j(p) ∈ Z_m on the jumps (p, i) ~ (σ_j(p), i + f_j(p)). From a point p in
copy 0 to a line L, the routes that exist for every pair are:

- inside the copy (H-distance ≤ 5): copy 0;
- early jump p → σ_j(p), then line–line ≤ 6: copy f_j(p);
- late up-jump p ⇝ σ_j⁻¹(L) (≤ 6) → L: copy f_j(σ_j⁻¹(L));
- late down-jump p ⇝ σ_j(x) (≤ 5) → x → L for x on L: copy −f_j(x);
- jump, jump down at the same line: p → σ_j(p) → z = σ_k⁻¹σ_j(p) (k ≠ j) ⇝ L (≤ 5): copy f_j(p) − f_k(z);
- early and late jump: p → σ_j(p) ⇝ σ_k⁻¹(L) (≤ 5) → L: copy f_j(p) + f_k(σ_k⁻¹(L)).

Point-point and line-line pairs have many more routes (jump at a point within distance 2 of either end).

**Proposition (Δ = q+2, m = q+3 copies).** Let r = 1, f: P → Z_m ∖ {0} injective on every line (so each line L misses
exactly one nonzero value γ_L), σ a bijection with f(σ⁻¹(L)) = −γ_L for every L, and assume the lines through any
point do not all miss the same value. Then the lift has diameter ≤ 8.
*Proof.* Point → line: copies {0} ∪ −f(L) ∪ {f(σ⁻¹L)} = Z_m by the routes above. Line ℓ → point t: ℓ → x → σ(x) ⇝ t
gives f(x) for x ∈ ℓ (length ≤ 1+1+5), ℓ → σ⁻¹(ℓ) ⇝ t gives −f(σ⁻¹ℓ) = γ_ℓ (≤ 1+6), and copy 0: all of Z_m.
Point → point: up at y with d(p,y) ≤ 2 (≤ 2+1+5) gives f(y), down at x with d(x,t) ≤ 2 (≤ 5+1+2) gives −f(x); the
lines through p miss at least two different values, so f(B₂(p)) = Z_m ∖ {0}. Line → line: ℓ → x → σ(x) ⇝ L (≤ 8)
gives f(ℓ), ℓ → σ⁻¹(ℓ) ⇝ L (≤ 6) gives γ_ℓ, and 0. ∎
Counting: each value class of f has N/(q+2) points, which needs (q+2) | N = (q+1)(q⁴+q²+1), i.e. (q+2) | 21:
q = 5 or 19. At q = 5 this is 8 copies, (7,8) with 62,496 vertices (squad card c8 tests it). It is weaker than the
q+4 copies that (13,8) suggests for Delorme's Δ = q+2 construction, and with two maps and zero incidence voltages
the same argument covers at most 2q+5 copies "for every source", below 5⌊(q+5)/2⌋.

## 4. What incidence voltages can and cannot do

With non-zero incidence voltages, an early (or late) jump to a vertex opposite the target brings a **bundle**: the
q+1 geodesics between two opposite vertices of H(q), with q+1 voltage sums. If every bundle had distinct sums, each
early/late jump would cover q+1 copies at once. But two geodesics of a bundle form an apartment (a 12-cycle), so
"all bundles rainbow" means every apartment has non-zero voltage, i.e. the k-fold cover of H(q) (incidence edges only)
has girth ≥ 14 and k ≥ q+1. Such a cover has (q+1)·2(q⁶−1)/(q−1) vertices or more, within a factor 1 + 1/q of the
girth-14 Moore bound 2(q⁷−1)/(q−1) for degree q+1: for q = 2 this is 378 < 384, the order of the (3,14)-cage, so it
cannot exist, and for larger q it would be a cage-quality graph (none is known). So bundles cannot be rainbow
everywhere; any construction at Delorme's level must use them only partly, or cover in another way.

## 4b. A "loop" design (∗-product with step sizes)

Writing Delorme's ∗-product H ∗ C_m with automorphism voltages k ↦ g + ψk and gauging the multipliers away gives an
equivalent cyclic lift: every vertex u of H(q) gets a loop with an odd voltage c(u) (lift edges (u,k) ~ (u, k ± c(u))),
incidence voltages are even, m is even, and the lift is bipartite by parity (colour = side(u) + k mod 2), Δ = q+3.
Along a geodesic, a loop step at the i-th vertex adds ±c(w_i), so coverage becomes a sumset condition. The bottleneck
is again point-line pairs at H-distance 5: even fibres are reached only by the geodesic with 0 or 2 loop steps (72
signed pairs of the 6 labels) and q walks of length 7, so m/2 ≤ 73 + q, a much larger bound than Delorme's count —
but it needs, on every such geodesic, the six labels' signed pair sums to cover 2Z_m nearly without repetition.
Random τ-invariant labels are far worse than two bijections (x2l.c, q = 5: cost 372, 4,278, 13,652 at m = 10, 16,
20, against 8 and 70 at M = 16, 20 for the bijection design), because each bottleneck pair has only ~80 walks instead of
~200. So this design is only useful with an exact algebraic labelling, which we do not have.

## 5. Octagons

The generalized octagons are GO(q, q²) and duals for q = 2^(2e+1). Only GO(2,4) (1,755 points, 2,925 lines, incidence
graph of 4,680 vertices with degrees 5 and 3, diameter 8) has small degree; the next one has degree 65. Covers of
GO(2,4) with the lines' two spare degrees used (line-line edges kept bipartite by a parity layer, 9,360 base vertices,
Δ = 5) have, by the same walk count as above (about 5·4⁸ reduced walks of length 9 from a vertex, coupon-collector
redundancy ≈ 13), room for about 5 fibre copies at D = 10, i.e. ≈ 47,000 vertices against our (5,10) record 95,472,
and less at D = 9. So octagon-based covers are not competitive for Δ ≤ 16.

## 6. Status

Open: the definition of Delorme's 5⌊(q+5)/2⌋ family; a structured voltage design that beats it at q = 7, 9, 11, 13.
A separate Opus agent is working on the theory (theory/NOTES.md when done). For (10,8), the Haar orbit search is
being retried with longer runs (HANDOFF.md).
