# Doubled-matching lifts of generalized quadrangles: 6·|GQ(q)| at (Δ, D) = (q+3, 5)

Job "cell-10-7" (Opus, cloud session, 2026-10-24), a spin-off of the (10,7) attack (research/squads/cells/d10D7.md).

## Construction

GQ = W(q), incidence graph B (points P, lines L, |P| = |L| = (q+1)(q²+1), (q+1)-regular, diameter 4, girth 8).
σ: P → L a bijection. Base multigraph: B plus every edge {p, σ(p)} twice. Voltages in Z₆: the two copies of
{p, σ(p)} get 1 and 4 (point → line); each flag (p, l) of the quadrangle gets 3ν(p, l), ν ∈ {0,1}. The lift has
vertices (x, h), h ∈ Z₆, and edges (x, h) ~ (y, h + g). It is bipartite, (q+3)-regular and has 12(q+1)(q²+1) vertices.

## Theorem (diameter ≤ 5 iff one condition on opposite pairs)

Write Z₆ = Z₂ × Z₃; the Z₃-coordinate of a walk is its signed number of matching jumps. All pairs below are base
vertices; "sheet" means an element of Z₆ (the lift is fibre-transitive, so sources (v, 0) suffice).
- Same-colour v, u: v → σ(v) → (geodesic, ≤ 3) → u reaches both sheets of Z₃-coset 1 (the two copies differ by 3).
  The reverse, a geodesic to σ(u) and then a back-jump, reaches coset 2. Length ≤ 4.
- If d(v,u) ≤ 2: the geodesic and the 2-cycle on v's doubled edge (+2 steps) reach both sheets of coset 0.
- Opposite colours (d ≤ 3): geodesic + 2-cycle (≤ 5) gives coset 0, v → σ(v) → geodesic (≤ 5) coset 1,
  v → geodesic to σ(p) for a point p on u, then the back-jump and one step (≤ 5) coset 2.
- d(v,u) = 4 (non-collinear points, or non-concurrent lines): cosets 1 and 2 as above. Coset 0 is reached iff
  (A) the q+1 geodesics v → u do not all have the same ν-parity, or (R) some walk of length ≤ 4 with jump sum
  ≡ 0 (mod 3) and at least one jump joins them.

So the lift has diameter ≤ 5 iff (A) or (R) holds for every pair at distance 4. `dmfast` (BASE=gq/gq_q{q}.bin
NPOLY=4) counts the pairs where both fail, exactly (checked against lift2's full lift cost). It anneals ν, with
exact incremental updates (a flag lies on 4q³ geodesics), and σ, by recomputing the routes. The same theorem holds
over generalized hexagons at D = 7, but counting rules that case out (research/squads/cells/d10D7.md §4).

## Why it works at D = 5

A random ν fails (A) on a fraction 2^−q of the pairs at distance 4, and routes cover only ≈ (q+1)/q² of them.
Expected bad pairs ≈ |pairs|·2^−q ≈ 10³ for q = 7..11, against dim H¹(W(q); Z₂) = q⁴ free bits (2,401 to 14,641). The
first moment is positive and joint annealing reaches 0 within minutes.

## Results (all: apsp.c VALID with diameter exactly 5, and lift2 DIAMETER_OK; checks/ has one CHECK.md each)

| cell | table (DS14v2) | previous best | new | base | random start → 0 |
|---|---|---|---|---|---|
| (10,5) | 4,000 | 4,000 | **4,800** | W(7) | 887 bad pairs; 2 runs, ~11 min |
| (11,5) | 5,850 | 5,850 | **7,020** | W(8) | 1,038; 2 runs, ~13 min |
| (12,5) | 8,200 | 8,748 (route-chart lift) | **9,840** | W(9) | 1,092; 1 run, ~10 min |
| (14,5) | 14,760 | 14,760 | 17,568 (running) | W(11) | 856 |

The table values in these cells are the polygon covers 5·|W(q)| (two plain matchings over Z₅). The doubled matching
gives a sixth sheet: +20 %.
Out of reach this way: (8,5) (q = 5: 1,872 < 2,048 ours), (16,5) (q = 13: 28,560 < 31,460 ours), and Δ − 3 not a
prime power: (9,5), (13,5), (15,5). Three parallel copies over Z₉ (Δ = q+4) need the q+1 geodesics to cover Z₃.
Counting rules that out at q ≤ 11: about 3·(2/3)^(q+1) of the pairs fail, against q⁴·ln 3 nats.
