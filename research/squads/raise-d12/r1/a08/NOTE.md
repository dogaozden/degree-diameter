# a08: (6,12) orbit structure at equal N (round 1)

Scale: N = |G| (graph has 2N vertices); target 2N > 9,366,240, i.e. N > 4,683,120. Tool: haar_sym, THREADS=1, RANDORB=120
(screen2.sh; candidate list cands.py). cost/k histogram bucket 31 = "overflow" (cost >= 155 for k = 5, cost >= 93 for k = 3).
Machine load was 16 on 4 cores, so all runs were short.

| card | group, orbit | N | mu | Fix | min | p10 | median | overflow (of 120) |
|---|---|---|---|---|---|---|---|---|
| (i)  | SL(2,32) x Z151, field x->x^2, "5 1 1" AFROB=1 | 4,943,136 | 21.5 | 5 | 25 | 47 | 186 | 65 (54%, cost >= 155) |
| (ii) | PSL(2,211) x Z1, conj order 5, "5 1 1" | 4,696,860 | 10.7 | 104 | 184 | 298 | 512 | 120 (100%, cost >= 155) |
| (ii) | PSL(2,19) x Z1381 (n prime = 1 mod 5), conj 5, "5 1 1" | 4,723,020 | 11.5 | 9 | 186 | 300 | 1136 | 120 (100%, cost >= 155) |
| (ii) | PSL(2,11) x Z7121, conj 5, "5 1 1" | 4,699,860 | 10.8 | 4 | 428,270 | 437,400 | 732,595 | 120 (100%, cost >= 155) |
| (iii)| PSL(2,211) x Z1, conj order 3, "3 2 0" (current structure type) | 4,696,860 | 10.7 | 104 | 7 | 15 | 34 | 31 (26%) |
| (iii)| PSL(2,79) x Z19, conj 3, "3 2 0" (current value's group) | 4,683,120 | 10.2 | 38 | 4 | 9 | 24 | 31 (26%) |

Not screened: PSL(2,31) x Z315 with conj 3 has |Fix| = 224 (r = 16 fixes 15 of the 315 z's). The annealer started at cost 4.2M
and stalled at 1.3M in 90 s, so it was dropped. "psl 32 x Z287" was a mistake in my candidate list: for even q, psl = sl,
so that group has N = 9.4M and is not a candidate. Only SL(2,32) x Z150/Z151 are at this size with the field automorphism.

## Findings
1. At equal N near 4.7M, conjugation of order 3 (the current structure) beats conjugation of order 5 by a wide margin: min 4-7
   against min 184-186 (100% overflow for order 5 in both PSL(2,211) and PSL(2,19)).
2. Order-5 conjugation is not rescued by a small centralizer: PSL(2,19) (|Fix| = 9) is as bad as PSL(2,211) (|Fix| = 104).
   The small-torus idea fails for a different reason: PSL(2,11) x Z7121 (|Fix| = 4) has cost ~4e5. My guess is that the
   Z_n coordinate is the bottleneck, because the z-sums of a radius-11 word lie in a small lattice of Z[zeta_5] mod n
   (n = 7121 is far too large for that). This is a guess, not checked.
3. Connectivity is not the problem: diag5.py finds <S^-1 S> = G in 12/12 random order-5 and order-3 sets on PSL(2,19).
4. The field structure (i) has the smallest Fix (5) and a clean lower tail (min 25 of 120) but a larger mu (21.5 at N = 4.94M).
   It is worse than order-3 conjugation at equal N. The smallest order-5 field candidate in range is SL(2,32) x Z150 (mu 19.6), which was not screened.
5. Annealing the order-3 structure on PSL(2,211) x 1 (90 s each, 3 seeds, about 420-450 evaluations): best cost 3, 1, 5.
   No cost-0 state, so nothing to check. Cost 1 is one uncovered B-element.

Verdict: no valid (6,12) graph above 9,366,240 from these structures. Order-5 inner conjugation is a clear negative with numbers.
Next: a larger RANDORB batch for order-3 PSL(2,211) x 1 (about 1000 samples, outside this box), and a cost-1 restart
from the seed-31 state if one is saved (haar_sym writes only cost-0 states).

Code and logs: screen2.sh, screen/*.log (RANDORB), anneal_*.log, cands.py, diag5.py, all in this folder.
