# w21 NOTES (handsoff-49): exhaustive minima for the best non-metacyclic groups

Start: 2026-11-01 01:25 UTC. Stop: 02:55 UTC.

## Plan
- exh2.c: w1's exhaustive scan (S = {e, r, b, c}, r = conjugacy class rep) plus a centraliser reduction:
  b runs over conjugation orbits of C_G(r) (orbit reps), c over all of G. Every set is conjugate to one of these, so
  the scan is still exhaustive up to inner automorphism. Expected work about N^2 evaluations per group, not N^2 per class.
- Each run: `timeout 540 nice -n 10 ./exh2 TABLE.bin BOUND R0 R1` with BOUND = known annealing cost + 1.

## Status
- (in progress)
