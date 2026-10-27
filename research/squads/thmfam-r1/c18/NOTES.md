# c18: repair the LPS family with extra letters (p=5, p=7)

Files: repair.py (extra lines, z=0, PGL mod q; alpha = conj by psi(1+i+j+k), which permutes i->j->k and leaves the LPS set invariant).
Extra letters tried: f_1pijk, f_ipjpk (fixed by alpha, +1), o_far, o_1i, o_2i, o_unip, o_u2, o_low, o_1p2i, o_i2 (alpha-orbits, +3).

Results (screen on 3 primes 29,41,53 for all; 7 primes 23,37,53,67,83,97,113 for the rest, because the machine was at load ~20):
- LPS p=5 Delta 6, full range 23..113: mean_excess 3.995 (matches 4.00). Subset: 3.661.
- p=5 +1 f_1pijk (Delta 7): full-range mean 4.434 (22 primes; first q=23 run), subset 4.578.
- p=5 +1 f_ipjpk (Delta 7): subset 4.172.
- p=5 +3 o_unip (Delta 9): subset 3.240 (best repair). 3-prime screen 2.91.
- p=5 +3 o_far (Delta 9): 3-prime screen 4.91 (worse). o_1i: 4.24 (3-prime). o_2i: 4.02 (3-prime).
- Random alpha-closed (gen_random_orb.py, group psl), same 7 primes:
  Delta 9 (f0 k3), seeds 1,2: 2.716, 2.859.  Delta 7 (f1 k2), seeds 1,2: 3.107, 3.107 (both seeds gave the same mean; not investigated).

Caveats: several repaired graphs report "connected: no" (component of (e,A) is half of the full graph); the scorer uses that component as the graph, as it does for LPS. p=7 was not scored (no subset run finished). Full-range scoring of o_unip was not run.

Answer: no formula repair tried here brings LPS to the random baseline at the new Delta. Best repair (o_unip, Delta 9) is 3.24 vs 2.72-2.86 for random.
