# B7 (wildcard, tools): exact alpha-orbit census and budget model for the k = 10 search

Card: wildcard tool that makes 157.8M (N = 78,917,652, psl 243 x Z11) or anything above 148.7M more likely within a few
core-hours. Budget 5 slot-min (used about 4). No VALID solution: score 0. Census and RANDORB runs in `census.log`.

## What was built

- `haar_sym_B7.c`: copy of research/structured/haar_sym.c with ONE added block in `orbit_main` (env `CENSUS=1`, after
  choose_alpha and the alpha checks, before scan_fix). For the chosen alpha it counts the elements of each alpha-orbit
  length L (orbit length of (x,z) = lcm of the Q-orbit length of x and the orbit length of z under z -> AR z), converts
  them to orbit counts, and prints the Poisson budget: an alpha-orbit of size L is uncovered with probability
  exp(-lam L/k), lam = W/N = 14.08. E_gen = (orbits of size k) exp(-lam), E_small = sum over L < k, P_small = exp(-E_small).
  No BFS, so a run costs about 5-10 s (setup dominated).
- `analyze.py`: turns the census lines into P(solution per sample) = (1 - p_deg) exp(-f E_gen - E_small) and core-hours to
  one solution at 0.40 s per sample, for an assumed excess factor f.
- `census_run3.sh`: the job that ran (3 census variants, RANDORB=60 for AFROBH with AR = 3 and with AR = 2 as control).
  `census.log` is its output.

## Census (exact, from `census.log`; N = 78,917,652, lam = 14.079, E_gen = 6.06 for every variant)

| alpha (k = 10) | Fix(alpha) minus e | orbits of size 1 / 2 / 5 | E_small | P_small |
|---|---|---|---|---|
| AFROB=1, AFROBH="0 1 2 0", AR=2 | 3 | 3 / 4 / 48 | 1.015 | 0.362 |
| AFROB=1, AFROBD=1, AR=2 (outer, A5) | 1 | 1 / 5 / 48 | 0.586 | 0.557 |
| AFROB=1, AFROBH="0 1 2 0", AR=3 | 3 | 3 / 4 / 536 | 1.443 | 0.236 |

The hand count agreed with the program (|Fix| and orbit counts). Only the z != 0 part changes between AR = 2 (all orbits
of size 10) and AR = 3 (orbits of size 5 for elements (x, z), x in C(h)). Full orbit lists are in `census.log`.

## RANDORB: is the clump excess tied to the z -> -z pairing? (60 samples each, same seed)

With AR = 2, alpha^5 = (conj by h, z -> -z), so the orbit generators come in pairs with opposite z. With AR = 3 the z-part
has order 5 and this pairing disappears.

| run | degenerate | non-degenerate | mean floor(cost/10) | approx. generic clumps | f = clumps / 6.06 |
|---|---|---|---|---|---|
| AFROBH, AR=2 (control) | 13/60 | 47 | 9.47 | 9.8 | 1.62 |
| AFROBH, AR=3 | 13/60 | 47 | 7.70 | 7.8 | 1.29 |

The difference (about 1.8 clumps) is about 2.8 sigma with 47 samples per arm. The earlier 40-sample AR=2 log
(`opus/randorb_psl243_11_k10h_frob1_ar2.log`) gives f about 1.6, the same value. The k = 5 Frobenius logs (64 samples) give
f about 1.05, so the random model fits k = 5.

## Time to one solution (analyze.py model, 22 % degenerate, 0.40 s per sample, no prefilter)

| variant | P_small | f | P(solution) per sample | expected core-hours |
|---|---|---|---|---|
| AFROBH, AR=2 (current Opus runs) | 0.36 | 1.62 | 1.6e-5 | about 7 |
| AFROBD, AR=2 (A5), excess unknown, assumed 1.62 | 0.56 | 1.62 | 2.4e-5 | about 4.6 |
| AFROBH, AR=3 | 0.24 | 1.29 | 7.5e-5 | about 1.5 |
| AFROBD, AR=3 (not run; predicted E_small 1.01) | 0.36 | 1.29 (assumed) | 1.2e-4 | about 1.0 |

A small-orbit prefilter (B1) would divide the times by about 2 to 3 (it rejects the samples with small-orbit misses at a
fraction of an evaluation). The k = 5 Frobenius family is about 50 times worse per sample (P0 about 1e-6 at f = 1.05, 0.31 s).

## Conclusion

1. The best lead from this card is AR = 3 on AFROBH: its small-orbit budget is worse (P_small 0.24 against 0.36), but the
   measured clump excess drops from 1.62 to 1.29, so the expected time to one solution falls from about 7 to about 1.5
   core-hours (about 4.7x). The f values rest on 47 samples per arm, so the factor is uncertain (roughly 2x to 7x).
   The Opus runs with AR = 2 (AFROB=1 and 3, AFROBH) should be checked against this; a RANDORB=500 run on AR = 3 would
   settle f to about 0.05.
2. AFROBD (outer involution, A5) has 1.5x the small-orbit success factor of AFROBH at equal excess, and the combination
   AFROBD with AR = 3 would have AFROBH-AR2's small budget. Neither was measured for the excess; this is the next test.
3. The random k = 10 route is the only brute-force option that fits a few core-hours. The k = 5 Frobenius random search is
   about 60x worse per sample (P about 1.2e-6 at f = 1.05, against 7.5e-5 for AR = 3); the k = 5 anneal is not modelled here.
4. No tool in B7's scope gives more than about 2.5x on its own within the budget. The alpha-quotient BFS (evaluate on
   alpha-orbit representatives, about 10x fewer states) is the largest speed lever left, but it does not fit the
   row-bitset layout of haar_sym (rows are cosets of a cyclic H of order 61, and alpha does not act on them by rotations).
   Not built.

## Notes

- Floor bias: RANDORB histograms are floor(cost/k). The clump means above add 0.5 for the floor and subtract the small-orbit
  misses (in clumps), which are 0.14 for AR = 2 and 0.36 for AR = 3.
- Degenerate samples: pure Frobenius without conjugation (AFROB=1, no AFROBH) gave 24/24 degenerate at cost 56.2M (71 % of
  N), so the conjugation by h is essential. With AFROBH about 22 % of samples are degenerate, for both AR = 2 and AR = 3.
