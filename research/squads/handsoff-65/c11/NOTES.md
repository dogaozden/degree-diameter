# c11 notes (round 2: 2+2 lifts with an imposed symmetry)

## Setup (17:45-18:00)
- Base: 2+2 vertices 0=A1,1=A2 (side 0), 2=B1,3=B2 (side 1); classes A=(0,2)xa, B=(0,3)x(6-a), C=(1,2)x(6-a), D=(1,3)xa.
- Group tables: tabs/sg_<order>_<id>.txt for orders 171..176, 180, 184, 186, 188, 190 (GAP, shared/gap_tables.g);
  tabs/cyc<m>.txt cyclic (mkcyc.py), tabs/id<m>.txt identity map (for side-preserving FMAP).
- tsym.c (C, built here): tabu like shared/tabu.c but voltages obey a symmetry from a SYM file:
  ptype 0 = free representative with partner p (ptype 1): volt(p) = f(volt(rep)); ptype 2 = self-fixed edge
  (volt in F = {g: f(g)=g}); f = inverse by default, FMAP=file gives another map. No gauge fixing (all reps free, INIT=random).
- Two symmetries (both verified numerically with verify_sym.py: (v,h) -> (sigma v, h) is an automorphism of the lift):
  * swap sigma: A1<->B2, A2<->B1 (sides exchanged), theta = id, f = inverse: mksym.py a pB pC  (pB, pC = number of
    2-cycles of sigma inside classes B and C; the other edges of those classes are sigma-fixed and need volt^2 = 1).
    Odd-order groups: only pB = pC = all-pairs works (no involutions).
  * side-preserving sigma' = (A1 A2)(B1 B2), theta = id, f = identity: mksym2.py a. Reps: 6, all full group.
- screen_sym.sh SECS ORDER ID "a:pB:pC ..." -> sym_screen.tsv (tabu SECS per run).
- Machine: keep runs <= 5 min per call, one at a time.

## Results
### Calibration on order 171 (swap, theta=id, 10 s each; sym_screen.tsv)
- best costs: C19:C9 (id 3) a2 all-pairs 8; C19:C9 (id 1) 12; C3x(C19:C3) (id 4, the group of the 684 graph) 16;
  other groups and options 144 and up. Cost 0 not reached.
### Cyclic calibration (5-8 s): unsymmetric tabu finds cost 0 at m=140 in ~3 s (2+2, a=2,3);
  swap-symmetric: 124-148 at m=140; side-preserving: 152 at m=140, 12 at m=100, 60 at m=120.
  => the symmetric subspace is much poorer for abelian groups (or tabu is weaker there).

### Order 176 swap (theta=id) screens: poor
- sym_screen.tsv (5 s each, 21 groups x {a2 p1q1, a2 p2q2}): best 52 (176/3 C8xD22), 60, 64 (176/16). 176/17 (C11:Q16) 84.
- 60 s runs: 176/17 a2p2q2: 88, 64; 176/3 a2p1q1: 52. The unsymmetric tabu reached 4 on 176/17. => theta = id is a bad symmetry.

### Key finding: swap sigma with f = INVERSE COMPOSED WITH theta = identity (f = identity map) on ABELIAN groups
- Symmetry: tau(v,h) = (sigma v, theta(h)) with theta = inversion (an automorphism for abelian G), so volt(sigma e) = volt(e).
  Realised by `mksym.py a 0 0` (B and C classes all sigma-fixed, free values; A<->D pairs) with FMAP=tabs/id<m>.txt.
- Cyclic calibration: m=100 (400 vertices): cost 0 in 0.1 s; m=120: 0.5 s; m=140 (n=560): cost 0 in 4 s.
  sw140.sol verified with shared/export_lift.py + shared/check.sh: bad=0, diam=5, n=560, RESULT VALID.
- Cyclic sweep, 8-20 s each (n = 4m): m=144: 8; 150: 4; 156: 24; 160: 28; 164: 36; 168: 60; 172: 44 (20 s).
  So cyclic groups stop near m = 145-150 with this tool.
- Non-cyclic abelian groups of orders 172..190: screen in ab_screen.tsv (10 s each, a = 1, 2, 3).
