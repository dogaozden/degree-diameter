# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-26 17:00–17:40 UTC: job fresh-6-5, round f65r1 (goal: beat bipartite (6,5) = 684)
Session: claude/bipartite-6-5-fresh-16bvjp (Opus director, 16 Haiku cards, effort high, 4-core box). Board:
`research/squads/f65r1/scoreboard.jsonl`; context and "already ruled out" list: `research/squads/f65r1/CONTEXT.md`.
Cost units differ by card (stated per line); every card's best is INVALID (diameter 6).
- c1 polynomial (Lazebnik–Ustimenko/Wenger) graphs on F7³+F7³ = 686: degree-6 rules ≈ 10,000 bad pairs (a 7-regular rule reaches 294).
- c2 lifts of random/simple bases h = 7…19 by cyclic/abelian groups: best lift cost 70 (h = 7, Heawood-type base, Z49); cost grows with h (h = 18–19: 400+).
- c3 lifts of bases h = 6…15 by non-abelian groups of order 24–60: best 119 (A5 h = 6; Z11⋊Z4 h = 8).
- c4 σ×α-symmetric 3+3 lifts, |Γ| = 115–130, α of order 3: best cost 2 at 702 (Γ = SmallGroup(117,1/2)). Director's note: these lifts are Haar graphs of Γ⋊Z3 (order 351), so this is the old Haar wall.
- c5 symmetric 2+2 lifts, |Γ| = 172–192, α of order 2: best 12 (Z31⋊Z6-type, 744). Haar graphs of Γ⋊Z2 for the same reason.
- c6 edge-swap annealing without symmetry from near misses: 686 (684 + 2 vertices) at 376 ordered bad pairs; the 702 orbit near miss is a deep local minimum (never improved).
- c7 "+2" surgery on the valid 684 graph: no edge of it is removable (every edge carries 44–63 pairs); best 144 unordered bad pairs.
- c8 hubs on the 630 chamber graph of PG(3,2) (+56 vertices): best 5,340 ordered bad pairs; 31 % of its same-side pairs have a unique walk of length ≤ 4.
- c9 Haar-like graphs of Chein (Moufang) loops, order 344–360: random samples far worse than groups (144k+); annealing starved of CPU.
- c10 structure-free annealing from random 686-vertex starts: 21,060 (random level).
- c11 literature: nothing above 684 since 2013; Feria-Purón–Pineda-Villavicencio give n_b(6,5) ≤ 1,556 (Moore − 6).
- c12 two-sided "mixed Cayley" graphs g ~ s·g, g·t on order 343: not measured (CPU starvation).
- c13 AG(3,7) lines of 7 parallel classes minus a matching: 18,888; structurally dead (some planes through each direction carry no second S-direction ⇒ ≥ 588 bad block pairs for any S).
- c14 Haar graphs with S invariant under a non-cyclic automorphism group (Z4, V4, S3, Z3²): best 52 (worse than cyclic order 3).
- c15 bi-coset graphs of products (A5×S3×Z3, PSL(2,7)×Z7, SL(2,5)×Z9, A5×A5, S6, …), L ≠ R allowed: best 35 (A5×S3×Z3, L = Z3, 720).
- c16 lifts of structured large bases (small Haar graphs, blown-up cubic graphs): best 88 (Haar(Z7) base, Z49, 686).
Director's own runs in the same window (exhaustive): orbit-symmetric Haar for all non-abelian groups of order 343–351,
α of order 2, 3, 5, 6: best cost 6 (SmallGroup(351,12) = Z3³⋊Z13, k = 3); coset graphs of 29 almost-simple groups: best
24 (PΓL(2,8), stabiliser of order 4, 378 per side); exhaustive Haar on Heis(7): none (A side alone always misses ≥ 4);
inverse-closed S (one condition S⁴ = G) on order 343 and (351,12): worse (min 20 / 6 uncovered).
Kept: nothing beats the Haar wall at N ≈ 351. Lesson: 16 CPU-bound cards on 4 cores starved each other (load 20–28;
c9 and c12 produced no measurement), and every symmetric lift with a side-transitive symmetry is just a Haar graph.
Next: the director's exhaustive orderly Haar search (all non-abelian groups of order 343–351) instead of more cards.
