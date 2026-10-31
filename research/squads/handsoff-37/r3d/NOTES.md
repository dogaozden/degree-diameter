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
