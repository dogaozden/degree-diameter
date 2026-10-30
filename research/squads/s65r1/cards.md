# Round s65r1 cards (goal: bipartite (6,5) graph on > 684 vertices)

Shared context, scorer, rules: CONTEXT.md. Director's own line meanwhile: exhaustive bi-Cayley campaign (bicay.c)
over all groups of order 344-360 (research/s65/bc_campaign/).

- **c1 tri-Cayley.** 3-orbit graphs of a group G of order 230-240 with an index-2 subgroup E, each orbit meeting both
  colours: vertices (g,i), i = 0,1,2, colour par(g) xor c_i; loops R_i (odd, inverse-closed), links S_ij. New code
  from bicay.c; annealing (exhaustive where small). 690-720 vertices.
- **c2 semi-exact 2+2 lifts.** vl.c with the last voltage solved exactly at every step (b4a2x idea): anneal 8
  voltages, pick the best w by tallying, over the missed elements, which w covers them. Few-involution groups of
  order 176-192 (C11 x Q16, C11:Q16, C11 x (C4:C4), C23:Q8, 3 x 64 groups with few involutions).
- **c3 3+3 lifts at 696-720.** Screen of all 6-regular 3x3 base matrices x groups of order 116, 117, 118, 120 with
  vl, longer anneals for the best pairs.
- **c4 alpha-invariant 2+2 lifts.** Voltage multisets invariant under an automorphism alpha of Gamma (order 2, 3, 4),
  acting on each parallel class (colour-preserving, fibre-fixing, so not a Haar graph); exhaustive over the reduced
  space. Gamma of order 172-192.
- **c5 |H| = 2 bi-coset sweep 686-702.** Every SmallGroup of order 686, 690, 692, 694, 696, 698, 700, 702 with a
  non-central involution, H = K (sweep_diag.sh, short anneals), then long anneals of the best five.
- **c6 non-solvable coset graphs.** Non-solvable, non-almost-simple groups: order 720 with |H| = 2, order 1080 with
  |H| = 3, order 1440 with |H| = 4 (720 vertices each), sweep.sh over all (H, K) classes.
- **c7 near-miss repair.** Delete k vertices from a structured near miss above 684 (Haar cost-2 graphs on 702-720
  vertices, or the 704-vertex lift at cost 14) and rewire the freed degree with a fast incremental annealer; bar
  to beat: 144 bad pairs at 686.
- **c8 wildcard.** Any construction or search none of c1-c7 or the ruled-out list uses.
