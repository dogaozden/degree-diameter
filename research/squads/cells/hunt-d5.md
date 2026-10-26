# Job hunt-d5: bipartite diameter-5 graphs at (5,5), (7,5), (9,5) (and (6,5))

Opus director with Haiku squads, cloud session_01G9FwCXeEt4mUvAMjcr9j11, branch `claude/hunt-d5-graphs-lh5vuj`,
2026-10-26 (started 13:04 UTC). 4 cores, 15 GB, shared by the squads and the director. Work folder:
`research/squads/hunt-d5/` (tools, rounds r1–r4, exact-search logs in `certs/`, finds in `finds/`).

## Result

**(9,5): 2,758 vertices** (ours was 2,662, table 2,496): the Haar graph of Z197 ⋊₁₀₄ Z7 (the non-abelian group of
order 1379), 9-regular, diameter 5. Solution `research/frontier/sols/d9D5_meta_197_7_104_s40164.txt`; checks in
`research/squads/hunt-d5/finds/d9D5_n2758_CHECK.txt` (build_haar2.py VALID; apsp.c all pairs RESULT VALID d=9 D=5
n=2758; haar5 on an independently built table: cost 0). Found by the director's seed farm (haar_fast, 8 s runs, K = 16,
COOL = 10, REHEAT = 40; seed 40164, cost 0 after 1.9 s; 1 cost-0 and 6 cost-2 runs in 181 seeds). Round 4 card c1 had
located the group (cost 2 in 2 of 26 seeds).

Earlier in the session: **2,756** on Z53 ⋊₁₆ Z26 = C2 × (C53 ⋊ C13) (SmallGroup(1378,2)), solution
`research/frontier/sols/d9D5_meta_53_26_16_s7058.txt`, checks in `finds/d9D5_n2756_CHECK.txt` (same three checks), director
farm seed 7058 (15 s runs) after the squads had located the group (round 2 c1: cost 4; round 3 c2, c3: cost 2).

(5,5), (7,5): no graph above our records (354, 1,152) yet; (6,5): no graph above the published 684 yet. Best near
misses and the exact negative results are below. [to be completed at the end of the session]

## What was tried (four squad rounds of 16 Haiku cards, logged in research/squads/LOG.md)

1. Haar graphs over every group of the windows (GAP SmallGroups, new: `tools/gapgroup.py`), annealing (`haar5`,
   `haar_fast`, `haar_tab`), orbit-symmetric S, exact searches.
2. Small-base voltage lifts (2+2, 3+3, 4+4, 5+5, 6+6, K_{Δ,Δ}), coset-union S, bi-coset graphs, GQ + matchings.
3. Route-chart lifts (Mizuno's controller × chart, bipartite form) for Δ = 3q.

What worked: metacyclic groups Z_p ⋊ Z_k (often × a small cyclic group) lead every cell, and many short annealing
seeds with near-miss saving beat long runs.

## Theorems and exact results

- **Route charts with 3 letters.** Over F₃⁴ and F₄⁴ there are 3-letter charts with every non-backtracking pattern
  nonsingular and both pencil conditions (`research/squads/hunt-d5/charts/chart_q3_u0.txt`, `tools/chartq.c`). So any
  cubic bipartite controller with same-side distance ≤ 4 and a 4-cycle through every vertex lifts to a
  3q-regular bipartite graph on 2q⁴m vertices with diameter ≤ 5 (checked all-pairs: m = 12, 16 at q = 3). The 4-cycles
  are necessary for q ≥ 3: closed backtracking walks at a vertex reach only 9 planes through the start, at most
  1 + 9(q² − 1) < q⁴ fibre points. For q ≥ 5 the pencil condition is impossible (5 directions, q + 1 ≥ 6 points). Such
  controllers: m = 16 found, m = 17 stalls at cost 6 in four independent searches (annealing, pattern-aware annealing,
  tabu, insertion from m = 16). So this family gives at most 2,592 at (9,5) in practice (below 2,662).
- **Diagonal obstruction for voltage lifts.** In a regular cover with group Γ ≠ 1 of a base of girth g, the vertices
  (v, e) and (v, γ) are at distance ≥ g (a shorter closed walk reduces to the trivial one). So a bipartite cover of
  diameter 5 needs a base of girth ≤ 4 or with parallel edges. (This sharpens the g − 1 bound of research/lifts:
  lifts of PG(2,q) incidence graphs have diameter ≥ 6, of GQs ≥ 8.)
- **Exact searches** (`research/squads/hunt-d5/certs/README.md`): no Haar graph at (5,5) for any group of order
  193–215 (179 groups) or 217–223; at (6,5) none for C71 ⋊ C5 (355), F₂₇ ⋊ C13 (351) or C17 × (C7 ⋊ C3) (357); at (7,5)
  every automorphism-symmetric S of SmallGroup(615,1) has cost ≥ 12.

## What failed and why

- Lifts of a GQ plus matchings: too few walks to the collinear points (counting); annealing far from 0.
- K_{Δ,Δ} lifts, small-base lifts with free voltages: costs 12–200, the restricted (Haar) voltages anneal better.
- Orbit-symmetric S at D = 5: always worse (exact minima ≥ 12 where plain annealing reached 4).
- Coset-union S and non-abelian coset fibres: product sets collapse (fewer distinct products).
- q = 2 route charts (for (6,5)): 3-letter charts keep 8 singular patterns and one side's diagonal fails; with a letter
  per edge (`tools/pelift.c`) the lift works on 4-cycle controllers (m ≤ 16, 512 vertices) but a few fibres keep a
  diagonal gap without 4-cycles.
