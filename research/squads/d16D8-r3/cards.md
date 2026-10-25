# d16D8 round 3 cards (Opus, 2026-10-25): symmetric repair on hexagons

c1 H(5), C_31: symrepair from random starts at m = 22..26 and warm-start chains (m -> m+1); largest VALID m.
   Targets: 25 (DGQ's count), 27 (an (8,8) record).
c2 H(5), C_31, different moves: copy symrepair.c and add C-equivariant matching moves (re-align one matching orbit, or
   swap the line orbits of two point orbits) and plain orbit-voltage Metropolis moves next to the repair moves.
c3 H(7), C_19: symrepair (evaluation ~5 s per step from 2,064 orbit sources); start at m = 18-22 and climb with warm
   starts. Targets 30 (DGQ), 31 (a (10,8) record).
c4 H(3), C_13: how far above DGQ's 20 does symmetric repair go (round 1 without symmetry: 28)? Calibration point.
c5 W(13), C_85: push symrepair beyond round 2's 28 (DGQ analog 45): longest runs, warm starts.
c6 W(q) scaling with symrepair at q = 7, 11 (groups from round 2 c4) and 13: m(q) slope vs DGQ's 2.5 per unit q.
c7 Twisted invariance (wildcard A): voltages psi(g.e) = u * psi(e) mod m for a unit u whose order divides the order of a
   subgroup of C, so C acts on the lift by (x, s) -> (g x, u s) and orbit sources stay exact; e.g. W(13) with the
   order-5 subgroup of C_85 and m in {11, 31, 41, 61}, or H(3) with C_13 and m = 53. Own builder; repair or anneal.
c8 Wildcard B: an approach none of c1-c7 uses, e.g. structured matchings (M_2 = M_1 composed with a power of the
   generator), larger or different groups (the order-7 or order-21 tori of H(5) if you can build them), two
   semiregular groups at once, or non-cyclic lift groups with your own checker.
