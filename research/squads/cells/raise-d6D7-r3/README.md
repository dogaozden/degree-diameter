# Round 3, raise-6-7 (cell (Δ, D) = (6, 7), record 8,880)

Partial snapshot, pushed while the metacyclic screen is still running. Status and verdicts go in ../raise-d6D7.md.

- `enum_meta.py LO HI`: lists metacyclic groups Z_m x|_r Z_K of order in [LO, HI] with an automorphism alpha(a,j) = (u a, j)
  of order k (k = 2..6) and Fix(alpha) = K * gcd(u-1, m) <= 3K.
- `jobs_meta_k12.txt`: the screen jobs (K >= 12, gcd(r-1, m) = 1; the K = 2 dihedral-type groups and K < 12 were dropped,
  as were r with gcd(r-1, m) > 1 that have a small abelian quotient). Filtering was done with a one-off python step.
- `screen.sh`: round 2's runner (RANDORB sampling per job, 4 parallel). Run as `./screen.sh jobs_meta_k12.txt meta_out <haar_sym> 100000`.
- `meta_summary.txt`: one line per job. `meta_out/`: per-job logs.
- `jobs_sporadic.txt`: the second batch (α of order 2, 4, 5, 6 on the large groups orb_screen lists; Heisenberg groups).
