# w03 IDEA: twisted product tpgl, Z_n x| PGL(2,29), at cell (10,9)

Cell (10,9): value 8,418,120 = 2N, N = 4,209,060, mu 42.4. No card of round 1 covers (10,9) (b-cards take 8,9,11-14;
m02 takes 15,16; w01 takes 12,13). Idea: the twisted product G = Z_n x| PGL(2,q) where a non-square determinant
inverts Z_n (haar_sym's existing `tpgl` family, never used at D = 9 in our records).

Why (odd-D theory, ODD_D_HOLES.md): in the direct product PGL(2,q) x Z_n the n central elements are missed with
prob ~exp(-lambda/h), h = 4, so they cost extra holes. The twist makes the centre trivial (z fixed by a non-square-det
element forces 2z = 0, impossible for odd n) and removes that term. Hypothesis: at equal N, tpgl beats pgl.
Calibration shape: q = 29, n = 173 (prime, odd): N = 29 (29^2-1) 173 = 4,214,280, vertices 8,428,560 (> 8,418,120),
mu = 43.1 (same range as the record shapes). Also run pgl 29 173 (direct product) at the same N as the control.
Plain random S (haar_sym, no ORBIT). Scorer: haarcheck_gen (sl/psl/prod only?) or build_haar2 / apsp on any hit.

## Results (1 thread, nice 10, plain random S, haar_sym K=8; cost = uncovered on both sides, D odd)
- (10,9), N = 4,214,280 (mu 43.1), 90-95 s runs:
  - tpgl 29 x Z173 (twisted): best 644 (seed 2), 685 (seed 3), 671 start-to-60 s trend; start cost 1874.
  - pgl 29 x Z173 (direct, control): best 84 (seed 2), 91 (seed 4, only 921 evals under load).
  - Verdict: the twist is much worse (about 7-8x the cost of the direct product). Hypothesis "twist removes the
    central holes, so tpgl wins" is FALSE at plain annealing. Likely cause (unverified): the Z_n coordinate of every
    word is a signed sum (inversion by det-odd letters), so the words spread over fewer Z_n values.
- Small-N sanity check (d=4, D=9, 40 s): tpgl 7 x Z5 (N=1680) cost 2 (no solution); pgl 7 x Z5 solved, verified by
  build_haar2 as VALID d=4 D=9 with 3360 vertices (file s_pgl_7_5.sol; not a record, record at d=4 is 4970).
  pgl 11 x Z7 (N=9240) and tpgl 11 x Z7 both at cost 5000+, out of range for d=4.
- No solution at (10,9). Record 8,418,120 not beaten.
- Second small-N pair, d=5, D=9, N=20,496 (40 s each): tpgl 7 x Z61 best 1177; pgl 7 x Z61 best 381. Same direction
  (twist about 3x worse). At N=1680 both are solved at once (too easy to compare).
