# r2f NOTES (worker r2f, round 2, card r2f: mixed free + non-free symmetry + exact search)

Start: 2026-10-31T17:36Z (date -u). Stop about 19:51Z (2h15); keep going until at least 19:36Z.

Plan: (1) find F21 = <g, s> in C168.1 (g order 7 free, s order 3 normalising <g>, 3 fixed vertices); (2) quotient by <g>
gives a 12+12 base with an order-3 base automorphism sigma; (3) symmetric SAT: lift over Z_m with s = (sigma, alpha),
E[a,b,t] <-> E[sigma a, sigma b, alpha t], sources reduced to sigma-orbit reps; (4) calibrate at n = 168, then 182, 196, 170.

## 17:37-17:45Z: structure of C168.1 (r2f/structf21.py, findf21.py)
- |Aut| = 504 with ONE normal Z7 (6 elements of order 7). Every order-3 element normalises it (s g s^-1 = g^r):
  112 order-3 elements with 3 fixed vertices have r = 2 or 4 (non-abelian F21 = Z7 x| Z3); 8 fixed-point-free ones have r = 1
  (Z21, free); 14 fixed-point-free with r = 2/4 (F21 free). So F21 with non-free s exists (card r2f step 1: yes).
- r2f/base_f21.py: the quotient by <g> with s-equivariant representatives (gauge c = 0): base 12+12, sigma on A has 3 fixed
  base vertices and 3 3-cycles, sigma on B has 4 3-cycles, alpha = r = 4. Lift check: r2f/lift_check_k12.edges far = 0
  (n = 168, diam 7). Base file: r2f/base_f21_k12.txt.
- r2f/symsat.py: SAT for Z_m lifts with an extra automorphism (sigma, alpha): E[a,b,t] <-> E[sigma a, sigma b, alpha t];
  sources reduced to sigma-orbit reps. Usage: symsat.py M K D ALPHA SIGMA_A_CYCLES SIGMA_B_CYCLES OUT [solver].

## 17:38-17:50Z: calibration results (n = 168, Z7 with F21 symmetry, alpha = 4, sigma A = 3 fixed + 3 3-cycles, B = 4 3-cycles)
- symsat.py, cadical195, no girth clauses: 371k vars, 738k clauses, 10 sources; NO answer in 540 s (timeout).
- Sanity check: FIXBASE=base_f21_k12.txt (pins the known C168.1 base, env FIXBASE in symsat.py) returns SAT in 0.0 s
  (the symmetric encoding and the walk/coverage constraints accept the known solution; the failure is search, not a bug).
- Next: G4=1 (lift girth >= 6 clauses, valid for this calibration because C168.1 has girth 12) with cadical, 540 s.
- G4=1 (2.2M clauses) calibration, cadical195, 540 s: NO answer (timeout). So plain symmetric SAT does not find the known
  F21 solution at n = 168 in 9 min. Decision (18:01Z): stop SAT for calibration; switch to a symmetric local search
  (r2f/symloc.c): G-invariant cubic graph, moves = orbit 2-switches (a switch and all its G-images), cost = far from one
  representative per G-orbit (weighted by orbit size). G = <z, s> with z the Z_m shift and s = (sigma, alpha), so this
  searches the same symmetric classes as the SAT. Start states from a degree-only SAT (no reachability clauses).

## 18:00-18:37Z: symmetric local search (symloc.c, symtabu.c) and results
- Calibration n=168 (F21, symloc SA, T 3 -> 0.3, random SAT start): far 0 (diam 7, apsp VALID) in 3 s. Logged as calib row.
  Z7-only (no s) on the same start: far 175 after 120 s (no calibration success). So the F21 class is much easier.
- n=170, Z5 with involution s (alpha = -1, sigma 1 fixed + 8 2-cycles per side): SA 350 (T 3, 240 s); 195 (T 20, 240 s);
  155 (T 60 -> 4, 120 s, seed 2). Not competitive with 46.
- n=170, Z15 (alpha = 1, sigma 2 fixed + 5 3-cycles): far 1500, lift disconnected; not useful (start is degenerate).
- n=182, F21 (alpha 2, sigma 1 fixed + 4 3-cycles per side, k = 13): SA from random start 231 (T 20 -> 1, 156 s).
- Orbit insertion from the verified n=168 F21 solution (r2f/surg182.py): one sigma-orbit of 3 base edges removed,
  fixed A and fixed B base vertices added (voltages alpha^i c0, alpha^i d0): best of 9 x 49 insertions far 434 (all pairs).
  SA repair (T 6 -> 0.5, 158 s): 301. Full-neighbourhood tabu (symtabu, 15-step tenure, 480 s, ~360 steps): 238.
- Z7-only SA at n = 182 from the same insertion start: stuck at 322 (acceptance almost zero at T 6).
- Verdict so far: no n >= 170 graph below the board (182 board 168 from c4; 170 board 46). Symmetric SA works at 168 but
  the orbit moves (21 switches for F21) are coarse: far jumps by 100+ per move, so SA/tabu stall above 150 for n >= 170.
