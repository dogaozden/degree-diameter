# Card A4: k = 5 Frobenius anneal, AFROB=4, different schedule (round d11D10-r2)

Target: psl 243 x Z11 (N = 78,917,652, 157,835,304 vertices), d = 11, D = 10, mu = 60.61, |Fix(alpha)| = 11 (+e).
Card: ORBIT="5 2 1" AFROB=4 ORBW=8 RESTART=1 TARGP=50 COOL=40, K = 12, SECONDS = 600, budget 12 slot-min.

## Commands

- Build (card folder, outside the gate, a few seconds): `gcc -O3 -march=native -fopenmp -o haar_sym_A4 haar_sym_A4.c -lm`.
  haar_sym_A4.c is research/structured/haar_sym.c plus one report line after the RESULT line:
  `A4FINAL best=<cost> bestE=<energy> uncovered_alpha_fixed_at_best=(bestE-best)/(ORBW-1)`. The search code is unchanged.
- Run (gated, background), seed 4 (the card gives no seed):
  `gate.sh 780 bash -c 'cd A4 && env ORBIT="5 2 1" AFROB=4 ORBW=8 RESTART=1 TARGP=50 COOL=40 ./haar_sym_A4 11 10 600 4 12 <A4>/d11D10_psl_243_11_orb5_frob4_s4.txt psl 243 11'`
  Log: A4/anneal_frob4_s4.log. THREADS unset (env -u THREADS not needed: THREADS was unset in the shell).
- Alpha as chosen by the code: Frobenius x -> x^81 on entries (order 5), z -> 3z on Z_11 (default AR = 3, the smallest r with r^5 = 1 mod 11).

## Status

- 12:52 UTC: gate queued (all 5 slots busy with Opus runs and A6 cards). Anneal not yet started.
