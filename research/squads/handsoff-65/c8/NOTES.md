# c8 notes (wildcard: generalized-hexagon quotients)
Plan: build H(5) (split Cayley hexagon, 3906 points, 3906 lines, GH(5,5) incidence graph 7812 vertices, diam 6)
from G2(5) 7-dim representation over F5 (3-form phi). Get G2(5) elements (Cayley transforms of g2 elements).
Quotient the incidence graph by a cyclic group K: orbits give n = #orbits; quotient diameter <= 5 needed.
Same-side pairs need distance <= 4 in the quotient, so it is a covering condition.

## 16:xx progress
- Built H(5) (split Cayley hexagon) in 7-dim model: g2 = Lie stabilizer of 3-form phi over F5 (dim 14), invariant form B,
  points = singular points (3906), lines = lines L with L inside W_z for all z in L (W_z = kernel of cross(z,.)): 3906 lines,
  distance distribution 1,6,30,150,750,3750,3125 (GH(5,5) incidence graph verified). Files: g2base.py lin.py g2lie.py hexgraph2.py
  g2grp.py (perm_of), quot.py (quotients), hexdata.pkl, rootel.pkl (152 unipotent elements of G2(5), exp(te)).
- Quotients of the GH(5,5) incidence graph by cyclic groups (run_cyc.py): n and far pairs
  order 7 n=1116 far 65349; order 6 n=1320 far 131974; order 8 n=996 far 46329; order 10 n=796 far 21325; order 12 n=666 far 11980.
  All diameter 6. Dead end for cyclic groups. Z3xZ3 (n=868) is the only remaining candidate and expected far pairs ~ 10^4.
- Next idea: induced subgraphs of GH(5,5) with diameter 5 (girth 12 means geodesics are unique; need no opposite same-side pairs).
- Cyclic quotients, sampled (run_cyc2.py): order 10 gives n=796/824/872 with far 21325..44740; order 8 gives n=996 far >= 46329;
  order 12 gives n=666 (far 11980) and 686 (far 13844); order 7 n=1116 far 65349. None close to 0.
- SA (sa.c, double edge swaps, cost = far pairs) on the n=872 order-10 quotient: 44618 -> 32657 in 150k steps. Hopeless.
- GQ(5,5)=W(5) lifts are provably dead: for a regular cover with group of order m, a collinear base pair u,v
  (unique non-backtracking 2-path, no non-backtracking 4-walk since GQ has no triangles) gives m^2-m lift pairs at distance >= 6.
  So bad >= (m^2-m)*4680 (m=2: 9360; m=3: 28080). Measured: Z2 lift SA 11780 at n=624 (lift_sa.c, gq.edges).
- Haar/bi-Cayley with index-2 bipartition = Haar graphs (closed for 686..800 except 768 by others).
- Z3xZ3 subgroup found (z3z3.py): quotient of H(5) by Z3xZ3 gives n=900, far 34392 (diam 6). Not useful.
- NEW family (dcsa.c): bipartite double covers B(Gamma) of general 6-regular non-bipartite Gamma on N vertices
  (Haar graphs = Cayley Gamma; non-Cayley Gamma is open). SA over Gamma with degree-preserving swaps, cost = far pairs of B(Gamma).
  Calibration plan: N=342 (n=684, Haar C6 x (C19:C3) is such a cover) must reach 0 before N=343 is trusted.
- n=686 (Z12 quotient) annealed by sa.c: far 13844 -> 9520 (150k steps). Logged on scoreboard. Not competitive.
- Z3xZ3 quotient n=900 far 34392. Orders 15,20,30 give n outside 600..1000 (run_cyc3.py). Dihedral D6 search (dihedral.py)
  found no inverting involution in 600 samples: not pursued.
- dcsa calibration: N=342 (where Haar 684 exists) reached only 7296 after 120k steps (dc342_sa1.err): generic SA over
  double covers cannot find the known 684 solution, so SA results at 686 from that family are not meaningful.
- Compound graphs: base/copy counting (Moore bounds for each factor) rules out copies of degree <=3 needed for 686.
- Summary: no graph with n > 684 and bad <= ~9500 was found; GH(5,5)-based families are far from diameter 5.
