# Job hunt-d5: bipartite diameter-5 graphs at (5,5), (7,5), (9,5) (and (6,5))

Opus director with Haiku squads, cloud session_01G9FwCXeEt4mUvAMjcr9j11, branch `claude/hunt-d5-graphs-lh5vuj`,
2026-10-26, 13:04–19:00 UTC. 4 cores, 15 GB, shared by the squads and the director. Work folder:
`research/squads/hunt-d5/` (tools, rounds r1–r6, exact-search logs in `certs/`, finds in `finds/`).

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

(5,5), (7,5): no graph above our records (354, 1,152); (6,5): no graph above the published 684. Instead, exact
negative results for every group that came close (below).

## Theorems and exact results

Certificates are in `research/squads/hunt-d5/certs/` (README there: method, sizes, positive controls).

- **(5,5): no Haar graph for any group of order 193–255** (all 1,028 groups; order 256 has 56,092 groups), by
  exhaustive search over all S ∋ e (`haar5 exhp`, probe-accelerated, exact for cost 0; positive control order 176 finds
  our 352-vertex graph; coverage checked group by group across the director's and the cards' logs). The squads' lifts of
  small bases stayed at cost ≥ 12. So a (5,5) Haar graph above 2·192 vertices needs a group of order ≥ 256 (where the
  size law already gives mu ≈ 67) or a non-Haar construction.
- **(6,5)**: no Haar graph for **every group of order 351** (all 14), SmallGroup(343,4), (355,1) = C71 ⋊ C5,
  (357,1) = C17 × (C7 ⋊ C3), (360,51) = C3 × SL(2,5), (360,88) and (360,136) (`haar5 complete` / `haar5 cert`,
  orbit-rank normalization). These are all the groups that reached cost ≤ 6 in the (6,5) screens (355/1, 351/5 and
  360/51 had cost 2; 360/136 had cost 4 in 31 of 31 seeds, each a different S).
- **(7,5)**: no Haar graph for SmallGroup(609,1) = C3 × (C29 ⋊ C7), (610,2) = C2 × (C61 ⋊ C5), (615,1) =
  C3 × (C41 ⋊ C5), (618,1) = C103 ⋊ C6, (618,2) = C2 × (C103 ⋊ C3) and (610,1) = C61 ⋊ C10: complete coset-pattern
  searches (next item; 2.2·10¹⁰, 7.6·10⁹, 1.3·10¹⁰, 5.0·10⁹, 5.0·10⁹ and 7.6·10⁹ sets). These are the groups with the best near
  misses: 610/2 and 615/1 had cost 2 in the farms (three and five times), 609/1 has the most even coset patterns of all
  (7,5) candidates. The exact searches got to cost 2 in three 609 patterns, never 0. SmallGroup(612,5) = C9 × (C17 ⋊ C4):
  its 29,274 best pattern classes have no solution (partial). The other groups of order 606–618 have only order-2
  actions on their large normal subgroup or failed the screens (best ≥ 7).
- **Coset-pattern search.** For G = (Z_p ⋊_r Z_k) × Z_n, the cosets of G' = Z_p met by S form a multiset J in
  Z_k × Z_n. The number W_t of words s_a⁻¹s_b s_c⁻¹s_d (non-backtracking) and s_a⁻¹s_b landing in coset t depends only
  on J (W = X₀ − 3(d−1)P + (d−1)²δ with P = F̃ ∗ F, X₀ = P ∗ P, F = multiplicities of J), and mu_J = Σ_t p·exp(−W_t/p)
  is the expected cost of a random S with pattern J. Up to isomorphism of the Haar graph one may take e ∈ S, one
  element of a non-kernel coset with a = 0 (conjugation by Z_p), and a second with a ∈ {0, 1} (automorphisms
  a ↦ ua); so each pattern is a product search of 2p^(d−3) sets (`tools/jpatterns.py`, `tools/jexact.py`,
  `haar5 prod`; positive control on an order-506 group recovers a known solution). This turns a farm on a group with
  p^(d−3) small enough into a complete answer: 609 (p = 29) is 21,279 patterns × 1.4·10⁶ sets, 610 (p = 61) 599 ×
  2.8·10⁷. mu_J also ranks groups: the best patterns have mu_J 46.3 for Z197 ⋊ Z7 (where the record was found), 47.6
  for 609/1, 47.8 for 610/2, 49.2 for 615/1, 49.9 for 618/2, 48.9 for 612/5, 49.6 for the best 1395 group. The 610
  cost-2 near misses and the 1379 solution sit at the most even patterns.
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
- At (7,5) every automorphism-symmetric S of SmallGroup(615,1) has cost ≥ 12, and the cost-2 and cost-4 sets of 615/1
  have no solution within 3 swaps.

## What was tried (six squad rounds, 82 Haiku cards, logged in research/squads/LOG.md)

1. Haar graphs over every group of the windows (GAP SmallGroups, `tools/gapgroup.py`), annealing (`haar5`,
   `haar_fast`, `haar_tab`), orbit-symmetric S, exact searches, seed farms with near-miss saving, exact LNS.
2. Small-base voltage lifts (2+2, 3+3, 4+4, 5+5, 6+6, K_{Δ,Δ}), coset-union S, bi-coset graphs, GQ + matchings.
3. Route-chart lifts (Mizuno's controller × chart, bipartite form) for Δ = 3q.
4. Coset-pattern exact searches (director, last two hours): 609/1, 610/1, 610/2, 615/1, 618/1, 618/2, 612/5 (top patterns);
   end-to-end completeness checks against brute force on six small groups (`certs/prod_completeness_checks.log`).

What worked: metacyclic groups Z_p ⋊ Z_k (often × a small cyclic group) with a large action order lead every cell;
many short annealing seeds (farms) beat long runs; at (9,5) the hit rate was about one cost-0 per 200 seeds of 8 s. The
squads found the right groups (screens), the director's farms and exact tools closed or settled them.

## What failed and why

- (7,5): every group of order 606–618 that came close is now proved empty (above); the rest stay at cost ≥ 7 in the
  screens (order-2 actions, small p, |G/G'| = 2). Above 618 mu grows by about 0.5 per order. So a larger (7,5) graph
  from this family needs a group these methods did not reach, or it is not a Haar graph.
- (5,5): Haar graphs are exhausted up to order 255; at Δ = 5 the size law is less favourable than at Δ = 9 (no
  solution even at mu ≈ 33), and lifts of small bases stay at cost ≥ 12.
- Lifts of a GQ plus matchings: too few walks to the collinear points (counting); annealing far from 0.
- K_{Δ,Δ} lifts, small-base lifts with free voltages: costs 12–200, the restricted (Haar) voltages anneal better.
- Orbit-symmetric S at D = 5: always worse (exact minima ≥ 12 where plain annealing reached 4).
- Coset-union S and non-abelian coset fibres: product sets collapse (fewer distinct products).
- Groups with |G/G'| = 2 (and dihedral-type groups): costs near N.
- q = 2 route charts (for (6,5)): 3-letter charts keep 8 singular patterns and one side's diagonal fails; with a letter
  per edge (`tools/pelift.c`) the lift works on 4-cycle controllers (m ≤ 16, 512 vertices) but a few fibres keep a
  diagonal gap without 4-cycles.
- Machine: autogroup scheduling was on (each shell its own scheduling group), so nice levels had no effect between jobs
  until 16:14; squads and farms shared the CPU about equally per launch, not by priority.

## End-of-job note

[to be filled at the end]
