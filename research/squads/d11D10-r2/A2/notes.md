# A2: what makes k = 10 RANDORB samples degenerate (psl 243 x Z11, AFROB=1 AFROBH="0 1 2 0" AR=2)

## Result

The degenerate samples are exactly the orbits whose generator x has z-coordinate 0 (all ten orbit elements lie in
PSL(2,243) x {0}). Then S is inside the index-11 subgroup G' = PSL(2,243) x {0}, the Haar graph splits into 11 copies,
and the B side reached from (e,A) is one copy only: cost = 10 |PSL(2,243)| = 71,743,320 (90.9 % of N = 78,917,652).
The cheap test is `x mod 11 == 0` (free). Skipping those orbits (SKIPZ=1 in random_orbit of haar_sym_A2.c) removes
every degenerate sample in the 100-sample test; the time per sample is unchanged (0.46 s).
The card's guess (order-122 generators, 20-27 %, cost about 56M) is refuted: see below.

## Commands and numbers (all through gate.sh; binary: A2/haar_sym_A2, source: A2/haar_sym_A2.c)

Base group (psl 243, n = 1, no Z11), same alpha and orbit rule, 1000 samples:
  `env ORBIT="10 1 1" AFROB=1 AFROBH="0 1 2 0" AR=2 RANDORB=1000 DUMP=1 ... haar_sym_A2 11 10 60 7 8 /dev/null psl 243 1`
  -> log base_randorb1000.log; cost 0 in 990, cost 1 in 9, cost 2 in 1; 0 degenerate. 46.8 s (0.047 s/sample).
  So the degeneracy is not a property of PSL(2,243) alone.

Lift, unrestricted (phase A), 100 samples, seed 7:
  `env ORBIT="10 1 1" AFROB=1 AFROBH="0 1 2 0" AR=2 RANDORB=100 DUMP=1 HISTFIRST=2 HISTMIN=1000000 haar_sym_A2 11 10 60 7 8 /dev/null psl 243 11`
  -> lift_A_unrestricted.log. min 24, p1 31, p10 63, median 111, mean 10,052,968. 46.9 s (0.47 s/sample).
  Degenerate (cost >= 1e6): 14 of 100. All 14 have z(x) = 0 (orbit z-values 0,0,...,0) and cost exactly 71,743,320.
  The other 86 all have z(x) != 0 (orbit z-values = all of 1..10 once) and cost 24 to about 200.
  Orders of x in the 14: 121 (9), 11 (2), 122 (2), 61 (1).

Refuted hypothesis (order 122): phase B, `... SKIPORD=122 RANDORB=100 ...` (lift_B_skip122.log): order-122
  generators are rejected (0 left), yet 13 of 100 samples are still degenerate, all with z(x) = 0 (orders 121, 11, 61).

SKIPZ patch (the fix), `... SKIPZ=1 RANDORB=100 DUMP=1 ...` (lift_D_skipz.log):
  15 orbits rejected (z = 0), 100 accepted: 0 degenerate (no cost near 7.2e7). min 24, p1 31, p10 60, median 100,
  mean 8,917 (the mean is set by 5 outliers, next paragraph). 46.0 s per 100 accepted samples (0.46 s/sample).
  (The counter line prints "skipped(order122)"; the label is wrong, the count is all rejections of the copy.)

Second, weaker class (not the z = 0 mode): in the SKIPZ run 5 of 100 samples have cost 8,770, 184,526, 185,018,
192,600 and 310,605 (orders 2, 61, 61, 121, 61). Not explained here; flag for a later card.

Phase C (SKIPORD=61) was started but aborted after the phase-A result (lift_C_skip61.log is partial, not used).

## Why z(x) = 0 is degenerate

z_i = 2^i z(x) (alpha multiplies z by AR = 2). If z(x) = 0 then all ten generators are in PSL(2,243) x {0}, so every
walk keeps z = 0 and the lift H(G,S) is 11 disjoint copies of H(PSL(2,243), S_Q). Random generators have z(x) = 0 with
probability 1/11 = 9.1 %; the 100-sample test gave 14 %. The base Haar graph itself is fine (above).

## Other facts used

- z-scaling (g,z) -> (g, mu z) is an automorphism of G that maps the sample with z0 to the one with mu z0 and the same
  Q-parts, so the cost depends only on the Q-part orbit. The z = 0 case is the only one with a separate cost value.
- Exact class densities in PSL(2,243): order 122 and order 61 each 24.6 % (1.76M of 7.17M elements); order 121 45 %.
  Sample frequencies (base, 1000): 25 %, 24 %, 46 %. The 20-27 % of the card matches these densities, not the lift.
- Cheap order tests kept in the code (a2_order122, a2_order61) were validated against exact orders on 300 base samples
  (0 mismatches); they are not needed for the fix.

## Files (all in A2/)

haar_sym_A2.c (copy of haar_sym.c with DUMP/HISTFIRST/HISTMIN/TRHIST instrumentation, SKIPORD=122|61, SKIPZ=1 in
random_orbit), haar_sym_A2 (binary), gf.py (GF(243) helpers), analyze.py, analyze_lift.py, logs as named above.
