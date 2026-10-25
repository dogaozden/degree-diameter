# A5: k = 10 outer involution (AFROBD=1), round d11D10-r2

Group psl 243 x Z11 (N = 78,917,652, mu = 60.61), ORBIT="10 1 1" AR=2: alpha has order 10, S = {e} + one orbit of size 10.
AFROBD=1 gives |Fix(alpha)| = 1 (+e) (haar_sym prints "fixed-point misses ~ 0.49"); AFROBH="0 1 2 0" gives 3 (+e) ("~ 0.98").

## Commands (gate.sh, RANDORB=150, seed 5, THREADS unset, all heavy runs gated)

    gate.sh 240 env ORBIT="10 1 1" AFROB=j AFROBD=1 AR=2 RANDORB=150 /home/user/degree-diameter/research/structured/haar_sym 11 10 60 5 8 /dev/null psl 243 11     (j = 1..4)

Drivers: run_screen.sh (chain A: j = 1..4), run_screen_b.sh (chain B), run_screen_c.sh (chain C); the status file is screen_status.txt.
The queue was long (each run waited 1-10 min for a slot), so chain B's copy of the j = 3 run was stopped before it ran, and
chain A's remaining j = 4 step was stopped in favour of chain C. Logs: randorb_frob{1,2,3,4}_d.log. Parser: analyze.py
(checked on opus/randorb_psl243_11_k10h_frob1_ar2.log: reproduces fix 3, 40 samples, 8 degenerate, non-degenerate mean 9.5).

Patched copy haar_sym_A5.c (binary haar_sym_A5; the only change is an env print SHOWLOW=c of the orbit generator of each sample with
cost <= c). Same seed, same samples: randorb_frob3_low_d.log (run_low.sh) and randorb_frob4_low_d.log (run_low4.sh) reproduce the
minima below.

## Numbers (RANDORB=150 each; cost = uncovered elements; clump = cost/10, floor)

| AFROB | fix | time s | min | p10 | median | degenerate (cost > 310) | non-degenerate n | mean clumps | median clumps | lowest costs (count) |
|---|---|---|---|---|---|---|---|---|---|---|
| 1 | 1 | 73.2 | 40 | 60 | 110 | 33/150 = 22.0 % | 117 | 10.32 | 10 | 40 (3) |
| 2 | 1 | 69.1 | 30 | 60 | 110 | 32/150 = 21.3 % | 118 | 9.86 | 9 | 30 (4), 33, 40 |
| 3 | 1 | 71.7 | 21 | 60 | 112 | 33/150 = 22.0 % | 117 | 9.73 | 9 | 21, 33, 40 (2) |
| 4 | 1 | 65.6 | 10 | 55 | 105 | 33/150 = 22.0 % | 117 | 9.68 | 9 | 10, 23, 30, 32, 33, 40 (4) |

Reruns with SHOWLOW (same samples): AFROB=3 cost 21 at sample 22, generator mat(31,90,189,197) z=1.
AFROB=4 cost 10 at sample 27, generator mat(88,168,122,27) z=3; cost 23 at sample 57, generator mat(148,159,110,122) z=8.

AFROBH comparison (A1's AR=2 logs, same parser, 100 samples each, fix 3):

| AFROB | min | degenerate | non-degenerate mean clumps | median | lowest costs |
|---|---|---|---|---|---|
| 1 | 20 | 18/100 | 10.07 | 10 | 20, 30, 33 |
| 2 | 30 | 19/100 | 10.40 | 10 | 30 |
| 3 | 21 | 18/100 | 9.79 | 9 | 21, 30, 35 |
| 4 | 41 | 18/100 | 10.23 | 10 | (none below 40) |

Opus log (AFROBH AFROB=1, 40 samples): min 31, degenerate 8/40, non-degenerate mean 9.5.

Pooled: AFROBD 600 samples: degenerate 21.8 %, non-degenerate mean 9.90 (n = 469), 3 samples below cost 30 (10, 21, 23).
AFROBH (A1 AR=2, 400 samples): degenerate 18.0 %, non-degenerate mean 10.12 (n = 327), 2 samples below cost 30 (20, 21).

## Conclusion

- AFROBD does not beat AFROBH. The bulk is level: non-degenerate mean 9.9 vs 10.1 clumps, medians 9-10. The degenerate fraction is
  slightly higher for AFROBD (21.8 % vs 18.0 %, about 1.5 standard errors). The lower tails are equal (3 of 600 vs 2 of 400 below cost 30).
- The lowest cost of the round so far is 10 (one clump, AFROBD AFROB=4), against 20 for AFROBH (AFROB=1). That is one sample in 600.
- Halving the alpha-fixed points (3 to 1, expected fixed-point misses 0.98 to 0.49) does not move the bulk, so the fixed points are
  not the bottleneck. The excess over mu/k = 6.06 clumps (about 9.9 measured) is elsewhere (see B3).
- The condition for RANDORB=1500 RANDB=1 RANDSTOP=1 ("beats every AFROBH pairing") is not met, so that search was not run.
  The remaining slot budget could not have covered it either.

## Budget

Six gated RANDORB runs, 411.9 s of slot time = 6.9 slot-min of the 8 allowed (waiting for slots not counted).
No solution written, so no checker run. No process of mine is still running.
