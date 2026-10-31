# r3d NOTES: polarity covers with a D5 symmetry at m = 85 (card r3d)

Start: 2026-10-31T19:25Z (date -u). Stop by 21:15Z, then final notes.

## Model (lift3d.c, written by r3d)
M = polarity graph on m = 5k vertices (u,x), x in Z5, cover G: A_i ~ B_j iff M_ij = 1, n = 2m.
D5 = <tau, sigma>: tau: x -> x+1, sigma: x -> -x (fixes (u,0) for every base vertex u). sigma-invariant M is a
quotient with these items (all voltages g in {1,2}, class = {g,-g}):
- F-edge {u,v}: M[(u,x),(v,x)] for all x (voltage 0, self-mirror).
- L1 at u: M-loop at every (u,x) (voltage 0).
- T-link {u,v} class g (u != v): M[(u,x),(v,x+-g)] for all x (a MIRROR PAIR of base edges, 2 stubs at each end).
- L2 at u, class g: M[(u,x),(u,x+-g)] for all x (2 stubs, self-mirror).
Slot types: u < A is type a (3 F-slots = F-edges + L1); u >= A is type b (1 F-slot + 1 T-slot = T-link or L2).
Moves (all stub-preserving, state checked after each accepted move): F 2-switch, L1 slide, F split/merge (L1 count +-2),
T 2-switch, T-link/L2 slide, T split/merge (L2 count +-2), class flip. SA on S with geometric T.

Cost, exact and cheap (per base source (u,0) only; translation and sigma invariance):
  c_u = #{j != (u,0): no even walk <= 6}, x_u = #{j: no odd walk <= 7}, S = sum_u (c_u + x_u),
  far(cover) = 5 S. Verified with bin/score37 on every file below (far = 5S exactly).
  Target far < 46 at n = 170 means S <= 9.

## Calibration (m = 80, n = 160; must reach S = 0)
- Random restarts / ILS (perturb best by 4 moves), 45 s runs, T 3 -> 0.3, 500k iters/restart:
  A = 9: S 10; A = 10: S 4 (far 20, file out/s80_A10_ils_best.edges, score37 far 20); A = 11: S 78;
  A = 8: S 30; A = 6: S 109; A = 4: S 229; A = 12: S 194; A = 14: S 872.
- Structural reason for the weak families: with A = 0 the F-edges and T-links form a 2-regular skeleton on the base,
  so M is a long cycle-like cover (diameter 16, S = 1360 for every restart). Small A is bad; A around 9-10 is best.
- So the D5 family does NOT reach 0 at m = 80 in these runs (the general Z5 family does, see r2c).

## m = 85 (n = 170) runs (score37 checked)
- A = 10: S 26 (far 130), 45 s ILS, file out/m85_A10_best.edges (diam 8). First r3d graph at 170.
- A = 9: S 30 (far 150); A = 11: S 36 (far 180); A = 12: S 150 (far 750).

## m = 85 (n = 170): A-scan with lift3d (45-90 s each, ILS or restarts; S = far/5)
| k | A (type a) | seeds / runs | best S | far |
|---|---|---|---|---|
| 17 | 7  | 1 | 130 | 650 |
| 17 | 8  | 1 | 72  | 360 |
| 17 | 9  | 3 (incl. 90 s) | 30 | 150 |
| 17 | 10 | 7 (45-90 s each, several seeds and schedules) | 26 | 130 |
| 17 | 11 | 1 | 36 | 180 |
| 17 | 12 | 1 | 150 | 750 |
All covers checked with bin/score37 (far = 5S exactly). A = 10 hits S = 26 in every run: a robust floor of this family.
Best n = 170 file: r3d/best170_D5_far130.edges (state r3d/best170_D5_far130.state), diam 8.
The first r3d graph at 170 is logged on the scoreboard (far 130). It does NOT beat the board (46 at 170).

## m = 80 calibration, more runs (A = 10, k = 16)
- 90 s ILS (pert 6): S = 4; 90 s hot start (T 8 -> 0.5, 2M sweeps): S = 4; 45 s ILS: S = 4. So floor S = 4 (far 20), not 0.
- Zero is reached by the general Z5 family (r2c lift2, c6), so the D5 restriction costs more than the calibration allows.

## Structure of the D5 family (why it is weak)
- Base skeleton: F-edges (single) + T-links (single) form a graph where type-a vertices have degree 3 and type-b vertices
  degree 2. With A = 0 it is a 2-regular skeleton: a cycle-like cover (diameter 16, S = 1360 in every run).
  So A must be large, but A = 17 leaves no T-link, and then M is disconnected (voltage 0 everywhere). A around 10 is the trade-off.
- Within a fixed A the SA always ends at the same floor, so it is not a search failure of a single seed.

## Generic orbit engine (gsym.c): built, checked, but NOT strong enough to calibrate
- gsym.c takes any permutation group on the m vertices (generator file, see gens/), state = edge-orbit representatives,
  moves = orbit 2-switch with random group elements on the new endpoints (stub-balanced), voltage moves (rep endpoint
  replaced by a group image), loop-pair moves (two loops <-> one edge). Cost = far over all sources (checked with score37).
- Unit test: the known zero-cost Z5 cover (r2c/calib160_lift2_zero.edges, 25 orbit reps) is accepted with far 0 at init.
- But from random starts it does not find zero for Z5 at m = 80: far 20-60 in 45-90 s runs (many settings tried:
  T scaled to orbit size, ILS, short/long restarts, with/without cross term, with/without volt and loop moves).
  Valid move rate is high (volt 99.8%, switch 95%), so the failure is in search strength, not in validity.
- Therefore its numbers for the F20 (Z5 x| Z4, base involution) and base-involution D5 families are NOT conclusive:
  F20p at m = 85: far 180 (90 s); D5p at m = 85: far 190 (85 s). Both worse than lift3d's 130; not competitive.
- F20 with the base fixed pointwise is impossible: a T-link (u,v,g) is mapped to (u,v,2g), so u would get 4 stubs toward v.
  F20 needs a base permutation pi of order 2 or 4 (generated in gens/F20p_k16.gen, F20p_k17.gen).

- Later additions (20:10-20:16Z): loop-pair moves ((p,p)+(q,q) <-> (p,q)), a sampled best-improvement tabu (env TABU=K,
  TTEN=tenure). Z5 m = 80 still stuck at far 40-60 (SA) and 90 (tabu from random, 60 s). Not calibrated; parked.

## Verdict for card r3d
- D5 with sigma fixing all base vertices (the card's family): floor far 130 at m = 85 (S = 26, A = 10), far 20 at m = 80
  (S = 4, not zero). Target far < 46 (S <= 9) NOT reached; no record. The D5 halving costs more than it saves: general
  Z5 gets far 80 at m = 85 and zero at m = 80.
- F20 and base-involution D5 with the generic engine: inconclusive (engine too weak; see above).

## Files
- lift3d.c (D5 fixed-base SA; usage in its header), gsym.c (generic orbit SA; usage in its header), lift2.c and lns.c (copies of r2c)
- best170_D5_far130.edges/.state (n = 170, far 130), calib160_D5_far20.edges (n = 160, far 20), out/ (all runs)
- scoreboard rows: first r3d graph at 170 (far 130) and the m = 80 calibration row (far 20, note "not zero").

## Next steps if someone continues this card
1. The fixed-base D5 family looks exhausted (floor 26 at 85). Do not spend more SA on it.
2. The generic engine needs a better search (e.g. tabu on the orbit 2-switch neighbourhood, or the lift2 move set
   in orbit form) before F20 or base-involution D5 are tested; calibrate it to zero at Z5 m = 80 first.

## Early hand-back (20:16Z)
The run was handed back at 20:16Z on a harness request, before the 21:15Z stop. A background batch of 8 lift3d runs (A=10, k=17, 200 s each, seeds 101-108) was still running; its logs are out/bg_A10_<seed>.log and out/bg_done.txt marks the end. Any result below S=26 there would be a new n=170 candidate: verify with bin/score37 before logging.
