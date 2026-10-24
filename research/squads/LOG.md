# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-24, cell-12-7 (Opus, cloud session claude/cell-12-7-search-k69h02), round d12D7-r1: beat (12,7) = 664,300

Goal: a bipartite graph of maximum degree 12 and diameter 7 on more than 664,300 vertices. Before the round Opus found
that the table value is 5·|H(9)| (polygon cover of the split Cayley hexagon H(9) with 2 matchings over Z5). It also
found the cell outside the reach of Haar search (ceiling 2N ≈ 522K), route-chart lifts, building graphs (D = 7
scan, negative) and lifts of the cover (3-route lemma). One squad of 8 (not 16: the machine has 4 cores and most cards
run annealers). Preamble and cards: research/squads/d12D7-r1/PREAMBLE.md, CARDS.md.

Cards: c1 Z2 "sheet lift" of H(q) × Z3 with two shift-1 matchings · c2 Z2-lift of the 5-copy cover (tests the lemma) ·
c3 local surgery on small polygon covers · c4 cubic route-chart controllers with a 6-cycle through every vertex ·
c5 literature / current table value · c6 wildcard at (7,7) · c7 wildcard at (12,7) · c8 wildcard, a new approach.

Best per card:
- c1: the sheet lift works at q = 2, 3 (4,368 vertices, Δ 6, apsp VALID, re-checked by Opus) and fails at q = 4
  (35,584 misses); its walk model predicts about 1 % uncovered at q = 9. Small-q effect, does not scale.
- c2: q = 2 best cost 1, q = 3 stuck near 20,600 (consistent with the lemma).
- c3: the annealed 6-copy cover of H(3) over Z6 has D = 7 (4,368), plus one vertex by surgery, 4,369 (apsp VALID). **Key
  observation: deleting a random edge of the 5-copy H(3) cover breaks only 0.4 pairs on average**, contradicting
  Opus's "every edge is critical" claim in the preamble.
- c4: cubic D = 7 controllers with a ≤ 6-cycle through every vertex reach m = 63 per side (K3,3 lift over Z7⋊Z3, apsp
  VALID, re-checked); route-chart lifts need m ≥ 82, so 516,096 at best. Without the cycle condition m = 84.
- c5: (pending at the time of writing).
- c6: PSL(2,29) Haar graph with an algebraic S, diameter 8; nothing structured beat 23,436 at (7,7).
- c7: abelian Haar graphs at (12,7) are capped at 146,654 vertices (exact count); AGL(1,p) with algebraic S behaves like
  random darts; best D = 7 graph 277,512.
- c8: failed (agent hit the output-token limit).

What Opus kept and did next: c3's observation. In the polygon cover the theorem's routes hop at an endpoint, so deleting
all hops at one point X breaks only pairs with an endpoint at X, σ1(X) or σ2(X). Opus deleted them, added 4 vertices
(two joined to X in all 5 copies, one joined to σ1(X), one to σ2(X) in all copies), and repaired the matchings so that
X and σ_t(X) reach everything without X's hops. Result: **664,304 vertices, Δ = 12, D = 7** (symcheck: copy shift
verified as an automorphism, BFS from all 132,864 orbit representatives, RESULT VALID). Then K gadgets with a
7-regular bipartite graph among the new vertices: K = 5 gives 664,320 (BFS from all special and new vertices clean).
Files: research/squads/d12D7/graphs/, research/squads/d12D7/opus/gadget.c, gadgetK.c, symcheck.c; write-up
research/squads/cells/d12D7.md. So the squad mattered: the record came from one card's side measurement, not from its
main score.
