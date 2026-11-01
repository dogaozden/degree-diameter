# Round 2 cards (raise-small-d, 2026-11-01)

Common: read research/squads/raise-small/HEADER.md first (rules and tools). $RS = research/frontier/raise_small.
Values to beat now: (3,13) 3,744, (3,14) 6,600, (3,12) 2,368, (3,11) 1,474, (3,10) 810, (4,9) 4,970, (4,10) 12,416,
(4,11) 30,334. CPU: load was ~19 on 4 cores in round 1, so every card got ~15 % of a core. Use short screens
(20-40 CPU-s) and spend the rest on chaining the 1-2 best states (START=...best). salift_s counts CPU seconds, so a
"90 s" run can take 4-5 minutes of wall time under load: keep SECS at 20-25 so each command ends within 110 s wall.

## What round 1 found (do not repeat)

- Joint base+voltage annealing (salift_s) over metacyclic groups Z_m x|_r Z_k is the method. Base size matters:
  at D = 13, 3+3 (p = 3) and 4+4 (p = 4) are best: p = 3 solves N = 609, 624 (n = 3,744) and has cost 2 at N = 630
  (Z7 x|_3 Z90) and 660 (Z11 x|_2 Z60), 4 at 684; p = 4 solves N = 462, 465, 468 (3,744) and has cost 2 at several
  468s, 31-48 at 474-486 (k = 6 groups). Big bases are worse: p = 5, 6 cost 6-28 at n = 3,660-4,104; p = 8, 10, 12
  cost 20-62 at n = 3,840-4,096.
- D = 14: p = 3 solves N = 1,081, 1,088, 1,092, 1,100 (Z11 x|_2 Z100, n = 6,600, the value); cost 2 at N = 1,168
  (Z73 x|_10 Z16) and 1,170 (Z195 x|_94 Z6), 6 at 1,197, 24 at 1,220. p = 2 solves N = 1,640 (Z41 x|_6 Z40, n = 6,560),
  cost 12 at 1,650. p = 4 cost 2 at 812, 816; p = 5, 6 cost 6-32 at n = 6,480-6,860.
- Group families: groups with small k (k = 6) or small r-order d are nearly abelian and do badly; large k / large d
  (Frobenius-like) solve fast. Non-metacyclic groups (AGL(1,q), SL(2,3) x Z20, A5 x Z_c, AGammaL(1,8) x Z5, wreath and
  Heisenberg groups) were not better than metacyclic at the same N (round 1 c04, c08).
- Cubic Cayley graphs of three involutions (PGL(2,q), S_7, products): diameter ~log2(n)+2, far below (c16).
- tabu1 (exhaustive 1-move tabu walk, bin/tabu1) did not close the cost-2 state at D = 13, N = 660 in 100 s.
- Δ = 4: quartic joint lifts (salift4) beat Haar random-S at the same n: (4,9) p = 2 over Z13 x|_2 Z96 (N = 1,248,
  n = 4,992) reached cost 18, while hmeta Haar at n = 5,008 had 150 (c12). The director chains that N = 1,248 state.
  (4,11): p = 3 cost 72 at n = 30,360 (Z230 x|_31 Z22, only ~9k evaluations), (4,12) p = 4 cost 80 at n = 74,088 (c13).
  A fixed GQ(3,3) base lifted by metacyclic voltages: cost 1,208 at (4,11) (c17). (4,13) Haar Z3851 x|_498 Z25 cost 2 at
  n = 192,550 (c14).
- Director scans running now (do not repeat): p = 4 at D = 13 over N = 469-560 (k >= 12); p = 3 at D = 14 over
  N = 1,171-1,300 (k >= 12); salift4 p = 2 chain at (4,9) on Z13 x|_2 Z96.

## Cards

- **d01 (3,13), p = 3, N = 625-720.** Groups with k >= 12 from glist.py; 20-s screens with 2 seeds; chain the best;
  also continue r1/c01's cost-2 states research/squads/raise-small/r1/c01/g630.sol.best (Z7 x|_3 Z90) and g660.sol.best
  (Z11 x|_2 Z60) with new seeds and lower T0 (4).
- **d02 (3,13), p = 2 (2+2 bases), N = 937-1,100** (n = 4N > 3,744; untried at D = 13). k >= 12 groups.
- **d03 (3,14), p = 3, N = 1,101-1,170.** Screens, and chain r1/c06's cost-2 state at N = 1,168 (Z73 x|_10 Z16; file
  research/squads/raise-small/r1/c06/ — find the .best with header "1168 1 3 2").
- **d04 (3,14), p = 2, N = 1,651-1,850** (n = 6,604-7,400). Screens then chains.
- **d07 (4,9), quartic p = 2 and p = 3, other groups.** salift4 (table from gtab.py) over metacyclic groups of order
  1,243-1,330 except Z13 x|_2 Z96 (p = 2, n = 4N > 4,970) and 829-900 (p = 3). Large k. Chain the best.
- **d08 (4,10), quartic p = 2, N = 3,105-3,300.** Use research/squads/raise-small/r1/c13/salift4m.c (metacyclic
  arithmetic, no table; read its header, compile into your folder) at D = 10. Also p = 3 at N = 2,070-2,200.
- **d09 (4,11), quartic p = 2, N = 7,584-7,900** with salift4m, D = 11; long chains on the best 1-2 groups.
- **d10 wildcard: orbit lifts.** Orbit search (S closed under a group automorphism) broke the random-S wall for Haar
  graphs at D = 7..10. Do the same for lifts: take a p+p cubic base with an automorphism sigma of order 3 (e.g. a 3+3
  base made of Z3-orbits of edges) and a group automorphism alpha of order 3 of Z_m x|_r Z_k (e.g. (a,j) -> (t a, j)
  with t^3 = 1 mod m, t != 1), and require voltage(sigma(e)) = alpha(voltage(e)). Write your own annealer (copy
  salift_s.c, constrain moves to edge orbits) and test it at (3,13) N = 630-700 (p = 3) or (3,14) N = 1,101-1,200.
