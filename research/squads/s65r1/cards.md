# Round s65r1 cards (goal: bipartite (6,5) graph on > 684 vertices)

Shared context, scorer, rules: CONTEXT.md. Director's own line meanwhile: exhaustive bi-Cayley campaign (bicay.c)
over all groups of order 344-360 (research/s65/bc_campaign/).

- **c1 tri-Cayley.** 3-orbit graphs of a group G of order 230-240 with an index-2 subgroup E, each orbit meeting both
  colours (the k = 3 analogue of the (5,5) record's family): vertices (g,i), i = 0,1,2, colour par(g) xor c_i;
  loops R_i (odd, inverse-closed), links S_ij (parity 1 xor c_i xor c_j). New code tri.c from bicay.c; annealing +
  exhaustive where small. 690-720 vertices.
- **c2 semi-exact 2+2 lifts.** b4a2x.c generalised to degree 6 and |Γ| <= 256 (bases [[2,4],[4,2]], [[3,3],[3,3]],
  [[1,5],[5,1]]): tree voltages 1, the last A1-B1 voltage w solved exactly from the missed elements, the other
  voltages annealed/random-restarted. Γ of order 172-180 (non-abelian; incl. GL(2,4) = C3 x A5 = SmallGroup(180,19)).
- **c3 semi-exact 3+3 lifts.** Same idea for 6-vertex bases (all 6-regular 3x3 multiplicity matrices), one voltage
  solved exactly, Γ of order 116-120 (incl. SL(2,5), S5, C2 x A5 at 120 -> 720 vertices).
- **c4 α-invariant 2+2 lifts.** Voltage multisets invariant under an automorphism α of Γ (order 2, 3 or 4) acting on
  each parallel class separately (colour-preserving, NOT side-transitive, so not a Haar graph); the reduced space is
  searched exhaustively. Γ of order 172-180.
- **c5 non-split coset graphs, solvable.** B(G; <t>, <t>) for involutions t not complemented by an index-2 subgroup,
  |G| = 686-718: continue the earlier scan (51 of 334 done, best 18), few-involution groups first; dcenum
  exhaustive/SA.
- **c6 coset graphs of non-solvable groups.** The non-almost-simple non-solvable groups of order 720 with |H| = 2
  (A5 x A4, S5 x S3, SL(2,5) x S3, A5 x D12, ...; 720 vertices) and of order 1080 with |H| = 3 (3.A6, A6 x C3,
  ...); dc2_export + dcenum.
- **c7 wildcard (combinatorial).** Any approach none of c1-c6 or the ruled-out list uses.
- **c8 wildcard (algebraic).** Any algebraic/geometric construction none of c1-c6 or the ruled-out list uses.
