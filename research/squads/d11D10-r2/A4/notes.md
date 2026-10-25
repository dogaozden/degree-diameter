# Card A4: k = 5 Frobenius anneal, AFROB=4, different schedule (round d11D10-r2)

Target: psl 243 x Z11 (N = 78,917,652, 157,835,304 vertices), d = 11, D = 10, mu = 60.61, |Fix(alpha)| = 11 (+e).
Card: ORBIT="5 2 1" AFROB=4 ORBW=8 RESTART=1 TARGP=50 COOL=40, K = 12, SECONDS = 600, budget 12 slot-min.

## Result

- No solution. Lowest cost 20 (raw uncovered elements: four generic alpha-orbits of size 5), 0 alpha-fixed uncovered
  elements at the best state. Reached by t = 31 s, never improved. 1597 evals, 129 steps (K = 12), RESULT time 601.8 s.
- The run ended normally (RESULT and A4FINAL printed) at about 13:06 UTC, before the 13:24 kill of haar_sym processes.
  No solution file was written, so no checker was run.

## Commands

- Build (card folder, a few seconds, run before the gate): `gcc -O3 -march=native -fopenmp -o haar_sym_A4 haar_sym_A4.c -lm`.
  haar_sym_A4.c is research/structured/haar_sym.c plus one report line after the RESULT line:
  `A4FINAL best=<cost> bestE=<energy> ... uncovered_alpha_fixed_at_best=(bestE-best)/(ORBW-1)`. The search code is unchanged.
- Run (gated, background, seed 4 since the card gives none):
  `gate.sh 780 bash -c 'cd A4 && env ORBIT="5 2 1" AFROB=4 ORBW=8 RESTART=1 TARGP=50 COOL=40 ./haar_sym_A4 11 10 600 4 12 <A4>/d11D10_psl_243_11_orb5_frob4_s4.txt psl 243 11'`
  Log: A4/anneal_frob4_s4.log. THREADS unset.
- The gate queued from 12:52 (all 5 slots busy) and got slot 3 at 12:56:18. Setup 2.6 s (+4.8 s for the wide rows).
- Alpha as chosen by the code: x -> x^81 on matrix entries (order 5), z -> 3z on Z_11 (default AR = 3, smallest r with r^5 = 1 mod 11).

## Cost trace (every ~2 min; full trace in anneal_frob4_s4.log; cost = current raw uncovered, best = lowest so far)

| t (s) | steps | evals | cost | best | T    |
|------:|------:|------:|-----:|-----:|------|
|    31 |     7 |    85 |   20 |   20 | 0.88 |
|    62 |    14 |   169 |   40 |   20 | 0.52 |
|    93 |    21 |   253 |   30 |   20 | 0.30 |
|   127 |    29 |   349 |   30 |   20 | 0.17 |
|   193 |    42 |   505 |   20 |   20 | 0.15 |
|   256 |    54 |   649 |   20 |   20 | 0.15 |
|   321 |    69 |   829 |   20 |   20 | 0.15 |
|   386 |    83 |   997 |   20 |   20 | 0.15 |
|   451 |    97 |  1165 |   20 |   20 | 0.15 |
|   518 |   113 |  1357 |   20 |   20 | 0.15 |
|   584 |   129 |  1549 |   20 |   20 | 0.15 |
| end   |   ~133|  1597 |   20 |   20 | 0.15 |

Start: cost 132, energy 146 (2 uncovered alpha-fixed elements, ORBW = 8 weight). End: RESULT best = 20, bestE = 20,
uncovered_alpha_fixed_at_best = 0.

## Conclusion

- The schedule as specified did not solve. The walk reached cost 20 within the first 7 steps. It then sat there from
  t = 161 s on, at the temperature floor TMIN = 0.15 (COOL = 40 halves T every 40 s from 1.5, reaching the floor at about
  t = 133 s). A move that raises the energy by one 5-element orbit has acceptance about exp(-1/0.15), so the walk only
  made neutral moves at cost 20.
- RESTART=1 never fired. The reheat in orbit_main needs both more than REHEAT = 150 s without improvement and more than
  REHEATSTEPS steps without improvement. REHEATSTEPS is not set by the card, so its code default of 400 applies. A 600 s run
  with K = 12 does only about 130 steps, so the reheat cannot trigger. The last 400+ s were spent at the T floor with no restart.
  A rerun of this schedule needs REHEATSTEPS of about 30-40 for restarts to happen. This is the main finding; the result of
  this one seed says nothing about AFROB=4 against AFROB=2 or 3.
- No more heavy runs, as the coordinator asked. The cell was solved at 157,835,304 by the k = 10 AR = 3 search (coordinator).
