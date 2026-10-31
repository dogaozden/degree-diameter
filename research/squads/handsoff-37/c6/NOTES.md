# c6 NOTES: canonical double covers of cubic graphs with loops (polarity)

Start: 2026-10-31T15:44:38Z (date -u). Stop about 17:44Z.

## Model
M = symmetric 0/1 matrix, m x m, row sums 3 (a loop M_ii = 1 counts once). Cover: A_i ~ B_j iff M_ij = 1, n = 2m.
Diameter <= 7 iff every pair i != j has an even walk of length <= 6 in M. Cost = #unordered pairs {i,j} with none
(far of the cover = 2 * cost). Cost is computed with 2-word bitsets: H-balls of radius 3 in the graph H where i~j
iff M^2_ij > 0 (ball_3(i) = union over j in B_i of ball_2(j)).

Plan: (1) code dc.c: SA over M with switch moves (edge 2-switch, loop pair <-> edge, loop slide); (2) calibrate m = 84
(n = 168); (3) m = 85 (n = 170) and up; (4) symmetry-imposed M; (5) tabu.

## 16:10Z results so far (all far = 2 * cost, verified with bin/score37 where noted)

Programs (in this folder):
- dc.c: plain SA over M (switches: edge 2-switch, loop pair -> edge, edge -> loop pair, loop slide). Full cost
  recompute per move (~2 us), about 500k moves/s at m=84. Usage: dc m seed seconds T0 T1 iters outprefix.
- dct.c: focused tabu (K candidates around a random uncovered pair, tabu on re-adding removed items, snapshot
  restore + kicks). Result: much WORSE than SA (cost 185 at m=84 in 40 s vs 58). Dropped.
- lift.c: Z_t-symmetric M (vertices (u,x), u < k, x in Z_t, m = k t): base multigraph on k vertices with voltages,
  zero loops (M-loop on every (u,x)). Moves: voltage change, base 2-switch with fresh voltages, zero-loop slide,
  zero-loop pair -> edge, edge -> zero loops. SA on the base, full cost on the lifted M. Usage:
  lift k t seed seconds T0 T1 iters outprefix [pert Tr0 Tr1] (pert > 0 = ILS restarts; did not help).

Calibration (cost = unordered uncovered pairs of M; far = 2*cost):
- Unstructured dc (no symmetry): m=70 cost 2 (58 s); m=76 cost 15; m=80 cost 37 (25 s each); m=84 cost 58 (60 s).
- Z_t lifts at m=84 (30 s each): (k,t)=(12,7): 42; (21,4): 44; (14,6): 54; (28,3): 66.
- Z_t lifts, zero cost found: m=70 (14,5) and (10,7) in < 30 s (far 0, apsp VALID for (14,5)).
  m=72 (12,6): cost 6 in 30 s. m=80 (16,5): cost 5 in 30 s, cost 0 in 70 s with 6M-iteration anneal.
  n=160 cover VALID (apsp), logged to scoreboard as calib: c6/best160_polarity_z5.edges.
- m=85 (n=170), the only free Z_t option with k >= 12 is t=5 (k=17): best cost 40 (far 80) in 60 s runs;
  45, 50, 60 for other temperatures/seeds. ILS restarts (pert 6 moves from restart best) gave 65: not better.

Structure of the m=80 zero solution: 10 M-loops, girth 7 (non-loop), every vertex's NB even-walk ball of radius 6
covers all other 79 same-side vertices.

Observation: cost changes come in multiples of t (free action), so temperature matters in units of t.

## 16:46Z update: what was run after 16:10 and where it stands

Engines: dc (plain SA on M), lift (Z_t lift SA, the main engine), lifttabu (tabu over Z_t lifts with full
neighbourhood of voltage changes plus sampled 2-switches; tabu_v forbids re-creating removed base edges).
dct (focused tabu on M) is much worse than SA (cost 185 vs 58 at m=84), dropped.

Zero-cost results (far = 0, cover of M, n = 2m):
- m=70 (n=140): lift k=14,t=5 and k=10,t=7; apsp VALID for k=14,t=5.
- m=75 (n=150): lift k=15,t=5 (odd k, so parity is not the obstruction), 70 s SA.
- m=80 (n=160): lift k=16,t=5, one of five 60-70 s SA runs (other four: cost 5, 25, 35). Valid (apsp), logged to
  scoreboard as calib: c6/best160_polarity_z5.edges.

Non-zero results (cost = unordered pairs, far = 2*cost):
- m=84 (n=168): (k,t)=(12,7) 42 in 40 s; (21,4) 44 in 30 s but 74 in 70 s; (14,6) 54 in 30 s but 84 in 70 s;
  (28,3) 66. Noisy: runs of the same config vary by 30+ across restarts.
- m=85 (n=170), the only free-action option with k >= 12 is t=5, k=17. About 12 runs (60-480 s, several T schedules,
  ILS restarts) all floor at cost 40 (far 80), except 45, 50, 55, 60, 65. Tabu (lifttabu, 300 s, 230k steps) reached
  40 at step 5.5k and never went lower. The floor solution has exactly 8 uncovered orbits (40 pairs) on 9 base
  vertices, 5 M-loops. Both engines land on the same floor, so the floor is probably structural in this family, not a
  search failure.
- m=90 (15,6), m=90 (18,5), m=91 (13,7), m=96 (12,8): cost 100-112 in 60 s. The frontier is about m = 80 to 84.
- Tabu at m=80 (16,5) reached only 5 in 90 s (SA hit 0 once), so the zeros are sparse; the landscape is rugged.

Verdict: the polarity model reaches n = 160 (zero cost) easily and sometimes n = 150, but no run reached cost 0 at
m >= 84 (n >= 168). No record (n > 168) found. Not logged to the scoreboard: nothing below the previous best at
n >= 170 (the only entry is the n = 160 calibration).

Next step if continued: start the Z_5 lift at m=85 from the cost-40 floor with a repair step that changes a whole
base vertex (all three of its stubs) at once; or try a second symmetry (order 4 automorphism acting on Z_5 by
multiplication by 2) to shrink the space to an exhaustive search.
