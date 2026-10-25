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

## 2026-10-25, cell-12-7 (Opus, resumed session claude/cell-12-7-resume-qxt4bj), round d12D7-r2: reach the cap, get past it

Before the round (Opus alone, about 1 hour): resumed from 664,304; master had 680,068 (cell-10-7 session). Opus found
(1) that freed points need not be pairwise non-collinear (a freed point has two hop points on each geodesic, at distance 2
and 4, so only collinear paths on two lines are forbidden; the 730-line Hermitian spread gives 7,300 freed points, the
maximum, against 4,291 before), (2) that the main graph alone then has diameter 7, so hubs may take owners from different
freed points at different levels, and (3) the cluster-assisted Haar hub graph (coset clusters on spread lines; every
relation is a left multiplication, so one weighted BFS from e decides all hub pairs; research/squads/d12D7/clhaar/).
Records on the way: 681,460, 683,452, 691,660, 693,100 (all checked; 683,452 and 693,100 plain all-pairs VALID). The
cap of the construction is 693,500 (14,600 hubs per side). Spin-off: (11,7) 413,180 (cap of the 3-level version).

Cards (preamble and cards: research/squads/d12D7-r2/): c1 order-14,600 groups (Z73 normal) · c2 order 14,520 with
mixing order-20 subgroups · c3 other orders in (14,400, 14,600] · c4 freeing matching edges beyond the spread ·
c5 hubs with 4 main edges · c6 non-Haar hub graphs past 14,400 · c7 wildcard: a different construction · c8 wildcard:
q = 3 test bed.

Best per card:
- c1: **14,600 = the cap**: Gamma = (Z73 x| Z8) x Z5^2, order-20 subgroups Z4 x Z5 and their Z73-conjugates, clhaarP cost 0
  in seconds. Opus rebuilt the graph from the card's layout: srccheck SOURCES OK, then plain all-pairs (apsp_mt)
  **RESULT VALID d=12 D=7 n=693,500, 12-regular.**
- c2: 14,520: GF(11)^2 x| SL(2,5) (order-20 subgroups = translation conjugates of Dic5); Opus rebuild, srccheck OK
  (693,340).
- c3: 14,560 (Z728 x| Z20), 14,500 (Z145 x| Z100), 14,440 (GF(361) x| C40), card's srccheck OK. Stalled: 14,580, 14,540
  (order-20 part acts on Z727 only by a sign), 14,480. Card's summary: cost 0 comes fast when the order-20 subgroups act
  with large order on every normal layer.
- c4: no extra matching edge frees with zero damage (40 extra points, both shifts, and 25 single edges all break pairs;
  cheapest about 1.3k pairs per edge).
- c6: no layout above 14,400 (200 extra hubs per side miss about 1,300 same-side hubs each; removing Haar edges to make
  room breaks old pairs).
- c8: q = 3 test bed reaches its cap 4,088 (apsp VALID) and nothing past it (4-main-edge hubs leave most hubs uncovered;
  none of the other 2,520 matching edges can be freed on top of the spread).
- c5: hubs with 4 main edges are dead: the best hub (level-0 owner removed, its 8 hub neighbours chosen by a coverage
  search, then swaps in the real graph) still misses 300 targets; the coverage model's floor with 8 neighbours is about
  232. (Opus's estimate before the round: about 9 % of the skipped level's lines uncovered.)
- c7: two copies of H(q), each minus a perfect matching, joined by two cross matchings (degree q+1, no hubs): never
  valid (q = 3: 8.4 % of pairs at distance > 7 after annealing; q = 5: 3.4 %). At q = 11 it would have 708,624
  vertices, but the small cases are far from working. Side note from the card: any nontrivial voltage lift of H(q)
  has diameter >= 8 (girth argument).

What Opus kept: c1's group (the cap, now the record) and c3's observation about mixing. Past the cap every attempt
is strongly negative (also Opus's own tests: deleting spread-line fibres 2.7e9 broken pairs, one extra freed point 82,720,
one deleted non-freed point fibre 1,568,770). The squad's main win was filling the last 1,100 hub slots per side
with groups Opus had not tried. Beating 693,500 needs a different family.
