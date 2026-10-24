# Beating 31,460 at (Δ, D) = (16, 5), bipartite

Job "beat-16-5" (Opus), branch `claude/beat-16-5-bipartite-px5cxt`. Started 2026-10-24.

Target: a bipartite graph with maximum degree 16 and diameter 5 on more than 31,460 vertices. The value to beat is
the bipartite flag graph C(2,3) of PG(4,3) (Cames van Batenburg–Korsky, arXiv:2608.03965), 15,730 + 15,730
vertices, 16-regular. Bipartite Moore bound: 2·(15⁵ − 1)/14 = 108,482, so 31,460 is 0.29 of it.

Scripts and outputs are in `beat165/`. Status lines are dated; newest last.

## 0. What a winner has to do (counting)

From a vertex, the non-backtracking walks of length ≤ 4 that end on the same side number
1 + 16·15 + 16·15³ = 54,241. Diameter 5 means these reach all N vertices of that side (opposite-side distances
≤ 5 follow). So N ≤ 54,241, and the average number of walks per target is 54,241/N. C(2,3) has
54,241/15,730 = 3.45. A graph with N > 15,730 per side needs fewer than 3.45 walks per target, with no target missed.

For random-like constructions this is far out of reach. The coupon-collector estimate of SIZE_LAW.md gives
μ = N·e^(−54,241/N) expected misses per source: μ ≈ 510 at N = 15,731, while searches solve at μ ≈ 10–40.
The size law puts a random-like Haar graph at (16,5) near N ≈ 9,000–9,500 (about 18,500 vertices), below even the
2013 table (27,300). So Haar search with random-like S cannot get near 31,460; only structure can.

## 1. Buildings: A₄(3) is the only one (checked exhaustively)

### 1.1 Partial-flag graphs ("residues meet")

`beat165/partflags.py`: every finite building of type A₂–A₇, B₂–B₆ (also with parameters (q,…,q,q²), (q²,…,q²,q),
(q²,…,q²,q³)), D₄–D₆, E₆, F₄ (also (q,q,q²,q²)), G₂ (also (q,q³)), q ≤ 16; side A = residues of type J, side B =
residues of type K, J ∪ K = S, adjacent when they meet. Max degree ≤ 16 and diameter ≤ 5: only A₄(3) with
J = {2,4}, K = {1,3} (31,460); every other hit has at most 146 vertices. (D ≤ 7 hits: GH(q), and D₄(3) with
(13,16)-degrees on 81,200 vertices, diameter 6.)

### 1.2 Any union of Weyl-distance classes as the adjacency

`beat165/hecke_cosets.py`: same buildings, side A = J-residues, side B = K-residues for all J, K (overlapping,
empty, equal), adjacency δ(R_A, R_B) ∈ Ω for every union Ω of (W_J, W_K)-double cosets with both degrees ≤ 16.
In a building the Weyl distances reachable by a walk with prescribed steps form the support of the product in
the Iwahori–Hecke algebra (structure constants ≥ 0), so diameter ≤ 5 iff Ω∘Ω⁻¹∘Ω∘Ω⁻¹ = W and Ω⁻¹∘Ω∘Ω⁻¹∘Ω = W.
This is exact, not a sample. Result for A₂–A₄, B₂, B₃ (all parameter sets above), G₂, I₂(8), q ≤ 16, keeping
graphs with ≥ 20,000 vertices: the only one with diameter ≤ 5 is A₄(3) with the flag relation. (331 configurations
with more than 31,460 vertices fail.) Larger types (A₅, A₆, B₄, B₅, D₄, D₅, F₄): running.

## 2. Affine and hyperbolic diagrams: room in the ball, no finite quotient in hand

`beat165/coxball.py`. For a 4-node diagram split {0,2} | {1,3}, the A-vertices within distance 2k of a vertex are the
J-residues at Weyl distance in W_J(W_K W_J)^k, counted by Σ q^ℓ(w)/16. At q = 3, radius 4:

| diagram (labels 01, 12, 23, 30) | radius 2 | radius 4 |
|---|---|---|
| A₄ (3,3,3,2) | 205 | 15,730 (= everything) |
| Ã₃ (3,3,3,3) | 241 | 33,883 |
| C̃₃ (4,3,4,2) | 205 | 28,744 |
| cycle (3,3,3,4) | 241 | 40,714 |
| cycle (4,4,4,4) | 241 | 52,945 |

C(2,3) differs from the Ã₃ flag graph in one place: its {1,4}-residues are K₄,₄ blocks (the source of all its 4-cycles),
where Ã₃ has projective planes. A finite quotient of the Ã₃ building whose flag graph keeps diameter 5 could have up
to 33,883 vertices per side. But it would need to be as "perfect" as a spherical building (each A-orbit hit by
≤ 2.15 ball elements on average, none missed); quotients by arithmetic lattices of PGL(4, F₃((t))) of that size would
be tiny solvable quotients (congruence subgroup property), which cover badly. Not pursued further yet.
