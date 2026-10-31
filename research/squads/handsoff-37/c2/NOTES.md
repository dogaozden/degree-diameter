# c2 NOTES (card c2: shrink the near misses)

Start: 2026-10-31T15:44:26Z (date -u). Stop about 17:44Z.

Plan: shrink.c = bit-parallel far cost (7 levels, all sources), 2-switch simulated annealing (half the moves focused
on vertices with far pairs), beam search over vertex-pair reductions (adjacent pair a~b, or any non-adjacent pair with
a perfect matching of their neighbourhoods), repeated down to n = 170.

## 15:55Z status (first 11 minutes)
- shrink.c built (cubic bipartite, A-first labels). far cost checked against bin/score37 on all four seeds (identical).
  Speed: one full far evaluation ~10 us at n=180 (100k 2-switch evaluations per ~10 s).
- Seed facts: far pairs of both n=180 near misses are ALL same-side pairs at distance exactly 8. c3xs3 (far 36): the
  36 far pairs form a 2-regular graph on 36 vertices; c30 (far 90): a perfect matching on all 180 vertices.
- Random 2-switches from the far-36 seed raise far by 41..100 (min seen 77 in 19k samples): the seed is a deep,
  rigid local minimum and every 2-switch perturbs most radius-6 balls.
- Runs (all failed to improve on the seed far 36 at n=180):
  * SA over 2-switches, T0=30..5 -> 0.1..2, 200k-1M steps: current far climbs to 300-1200 at high T, cools to ~300
    at T=1 (SA from this rugged landscape is useless). Focus on far vertices: same.
  * Tabu, best-of-300 focused 2-switches per step, tenure 15, 3000 steps: best stays 36.
  * ILS: 6 random focused switches then 150 tabu steps, 30 rounds: never below the kicked state (far 450+).
  * Sampled compound moves at 180 (200k pairs, 1M triples, 1M quadruples of focused 2-switches): none below 36.
- Reductions (delete a~b or any non-adjacent a,b, match the leftover neighbours; beam width 20, greedy on far):
  * 180 -> 178 best single reduction 106 (adjacent only), 98 with non-adjacent; beam reaches 86 at n=176, then 97..106
    at 174..170 without repair. With 30k-step SA per beam member after each level: n=170 far 83 (run b2).
  * Seed nm192 Haar (far 384): beam reduction to 180 gives far 360 (no good).

## 16:04Z: equivariant reductions (new idea, eqred.py)
- Automorphism groups (networkx VF2, out/auts_*.json): nm180_c30 has |Aut| = 30 (regular C30, free). nm180_c3xs3 has
  |Aut| = 144: 26 free elements of order 3, 27 free involutions, 24 free elements of order 4, 42 of order 6, plus
  non-free involutions (fixing 12 or 24 vertices).
- eqred.py: pick tau of order h (free), remove one tau-orbit on A and one on B (2h vertices), rewire the loose slots by
  every tau-equivariant perfect matching (new edges must not already exist), score each candidate with `shrink stream`.
  h = 5 on c30 gives n = 170 (a C5-lift with base 17+17, the open case of cards c3/c4); h = 2 gives 176 and h = 3 gives
  174 on c30; h = 4 on c3xs3 gives 172, h = 3 gives 174.
- Bug found and fixed: the stream mode did not flush stdout, so the Python driver deadlocked (fixed in shrink.c).

## 16:08Z: more negative results (all far > 36 at 180; reductions stay near 80-120)
- k-edge heat-bath LNS (shrink lns; remove k edges with distinct ends inside a radius-3 ball, reconnect by any valid
  permutation, draw one with weight exp(-far/T)), k = 4, 20000 steps: at T0 = 2 the chain stays at far 36 (every other
  reconnection costs >= 40); at T0 = 20 -> 1 the equilibrium far is ~320-630. Same rugged landscape as 2-switches.
  (Bug found on the way: radius-2 balls have 7 A-vertices and 3 B-vertices, so no 4-matching exists; use radius 3.)
- Wide beam (width 540, adjacent pairs, no SA): 178 -> 106, 176 -> 96, 174 -> 97, 172 -> 100, 170 -> 102. The narrow
  beam (width 20, non-adjacent) reached 86 at 176 and 83 at 170 after SA. So greedy shrinking saturates near 80-100.
- Equivariant reductions (eqred.py), each candidate scored exactly:
  * c30 seed, C5 (h = 5): n = 170, 198780 equivariant candidates, best far 115 (out/eq170c30_rank0_far115.edges).
  * c30 seed, C3 (h = 3): n = 174, best far 123. C2 (h = 2): n = 176, best far 178 (the involution is one
    of the 15 orbit-pair structures; the free involution gives poor reductions).
  * c3xs3 seed, C3 (h = 3, free, side-preserving): n = 174, best far 102.
  * c3xs3, h = 2 and h = 4 need side-preserving free elements (an order-4 element first chosen swapped the sides; fixed).
- Other reference: at n = 170 the best far on the board is c8's 46 (LNS from conder168 + inserted pair), so the
  reductions from the 180 seeds are clearly worse than growing from the 168 graph.

## 16:12Z: exact local optimality of the seeds (shrink kopt, exhaustive)
- Exhaustive 2-switch neighbourhood (all 35775 edge pairs with distinct ends, both reconnections): c3xs3 seed (far 36):
  min far over the neighbourhood = 77 (144 moves reach it); c30 seed (far 90): min 109. No 2-switch improves either seed
  or even keeps it: the far-36 point is an isolated strict local minimum (every neighbour is +41 or worse).
- Haar seed (n = 192): VF2 cannot find a single automorphism with a prescribed image of vertex 0 within 150 s (the graph
  is too symmetric for the naive search), so the order-h symmetric reductions of the Haar seed were not run. Its greedy
  reduction to 180 is already 360, far above anything useful, so this was dropped.
- Equivariant reduction of c3xs3 by a free side-preserving C2 (176): best 142; the order-4 elements are all side-swapping
  or not fully free, so no C4 reduction to 172 exists for this group.

## 16:18Z: more neighbourhoods, all worse than or equal to the seeds
- Exhaustive 3-edge reconnection neighbourhood of the c3xs3 seed (3.1M edge triples, 14.9M reconnections): min far 77,
  nothing <= 36. Exhaustive 2-edge neighbourhoods of the best reduced graphs: best170 (far 83) -> min 86; best176
  (far 86) -> min 103; eq170 C5 (far 115) -> min 116; eq174 C3 (far 102) -> min 114. Every reduced graph is a strict
  local minimum for 2-switches.
- Ball deletion with rematching (shrink ballred): delete 5 A + 5 B vertices in BFS order around a centre, rewire the
  loose slots by a bijection optimised by annealing over swaps (2000 and 30000 steps, all 180 centres):
  best far 156 (c3xs3), 157 (c30). Sequential pair reductions (83 at 170) beat it: one pair reduction changes fewer balls.
- Beam from the symmetric 174 (eq174, far 102) to 170 with SA 30k: far 94 (not better than 83).
- Running now: beam width 40, SA 100k per member, non-adjacent reductions (out/big40.log).

## 16:27Z: wide annealed beam and perturbed restarts
- Beam width 40, SA 100k per member, non-adjacent reductions (out/big40.log): 178 -> 98, 176 -> 86, 174 -> 97,
  172 -> 106, 170 -> 94. More SA does not help; the beam saturates.
- Perturbed restarts (shrink beam with PERTURB=k: k random 2-switches on the 180 seed before the beam, width 10, SA 20k,
  seeds 100..159, results in out/pt_results.txt): running.

## 16:43Z: perturbed restarts found far 80 at n=170 (new best, logged)
- Batch 1 (seeds 100..159, PERTURB = 2/4/6 random switches, beam width 10, SA 20k): 56 finished; far values at 170:
  80 (1 run, seed 135, k=2), 83 (2), 86 (8), 89 (2), 94, 97, 101, 102 (2), ...; many runs reach the same 83 or 86.
  The far-80 graph: out/pt135_n170_far80.edges, copied to c2/best170.edges, verified by bin/score37 (far 80, diam 8).
- Batch 2 (seeds 200..279, both seeds alternating, k = 1..3): running, out/pt2_results.txt.

## 17:07Z: batch 2 gave far 76 at n=170 (src = c30 seed, seed 261, k = 1; out/pb261_n170_far76.edges), now c2/best170.edges,
verified by bin/score37 (far 76, diam 8), logged to the scoreboard. Batch 2 distribution: 76 (1), 80 (1), 82 (1), 83 (7), 86 (...).
Batch 3 (seeds 300..359, k = 1 or 2, both seeds): running, out/pt3_results.txt.

## 17:24Z: final state (card c2 stops about 17:44Z)
- Best per n (all verified with bin/score37; all logged to scoreboard.tsv):
  n=170 far 76 (c2/best170.edges; found twice, seeds 261 and 308, from the c30 seed with one random switch first),
  n=172 far 106, n=174 far 97, n=176 far 86, n=178 far 98 (c2/best17x.edges: pair-reduction beams from the c3xs3 seed).
  n=180 far 36 and n=192 far 384 (no improvement; the seeds are exact local minima for 2- and 3-edge reconnections).
- No far 0 at any n >= 170, so nothing to copy to records/.
- Recipe for the far-76 graph: shrink beam IN=nm180_c30_b31.edges target 170 width 10 SA 20000 T 2->0.3 seed 261,
  PERTURB=1 (one random switch on the seed first, then pair reductions to n=170 with SA after each level).
- What did not work (numbers in the sections above): SA / tabu / ILS / sampled compound moves / k-edge heat-bath LNS on
  the 180 seeds (far stays 36 or climbs to 300+), equivariant reductions (C5: 115, C3: 102 and 123, C2: 142 and 178),
  ball deletion with rematching (156), wide beams (94..106).
- Diagnosis: the far landscape is rugged. Every reduced graph here is a strict local minimum for exhaustive 2-switches
  (the best 2-switch neighbour is 3 to 10 worse), so local moves cannot descend; restarts with one perturbation and a
  fresh pair-reduction beam are the only thing that moved the best (83 -> 80 -> 76).
- Next step (not done here): restarts are cheap (~15 s each), so many more restarts (k=1, both seeds, width 10) might
  push 170 below 76; a real improvement needs a different structure (grow from the 168 graph, as c8 does with 46).
