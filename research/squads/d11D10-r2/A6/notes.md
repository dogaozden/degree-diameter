# Card A6: conjugation-family fallbacks (psl 71 x Z421, psl 79 x Z311)

Start 12:49:19 UTC, time box 40 min (ends 13:29 UTC). Budget 12 slot-min; used 11.75 (slot3 352 s = 5.87, slot4 353 s = 5.88).

## Conclusion

No solution. Neither group reached cost 0 in one 330 s anneal (985 and 1049 evaluations). Lowest raw cost: 5 for psl 71 x Z421
(one uncovered alpha-orbit of 5 elements, zero alpha-fixed misses) and 10 for psl 79 x Z311 (two uncovered orbits). No solution
file was written, so the score is 0 and haarcheck_psl had nothing to check.

RESTART=1 never fired. A reheat needs 150 s without gain AND more than REHEATSTEPS=400 steps since the last gain. A 330 s run
makes only 123 steps (psl 71) and 131 steps (psl 79), so the step condition is never met. T falls to TMIN = 0.15 by about 95 s
and stays there. At T = 0.15 a move one clump worse is accepted with probability exp(-1/0.15) = 0.001, so after about 95 s the
search was effectively greedy.

## Targets

| group | N = \|G\| | vertices 2N | mu | mu/k | alpha (from log) | \|Fix(alpha)\| |
|---|---|---|---|---|---|---|
| psl 71 x Z421 | 75,325,320 | 150,650,640 | 29.56 | 5.91 | conj by mat(2,69,29,7), z -> 252 z on Z421 | 34 (+e) |
| psl 79 x Z311 | 76,655,280 | 153,310,560 | 38.86 | 7.77 | conj by mat(11,66,63,19), z -> 6 z on Z311 | 39 (+e) |

71 = 1 (mod 5), 79 = -1 (mod 5), and 421, 311 are prime with n = 1 (mod 5), so ORBIT="5 2 1" applies. haar_sym's choose_alpha
picked AR = 252 and AR = 6. Both have order 5 mod n (6^5 = 7776 = 1 mod 311).

## Commands (both through gate.sh, THREADS unset via env -u, run in parallel)

    /home/user/degree-diameter/research/squads/d11D10-r2/gate.sh 450 env -u THREADS ORBIT="5 2 1" ORBW=10 RESTART=1 /home/user/degree-diameter/research/structured/haar_sym 11 10 330 6 8 /home/user/degree-diameter/research/squads/d11D10-r2/A6/d11D10_psl_71_421_orb5_A6_s6.txt psl 71 421
    /home/user/degree-diameter/research/squads/d11D10-r2/gate.sh 450 env -u THREADS ORBIT="5 2 1" ORBW=10 RESTART=1 /home/user/degree-diameter/research/structured/haar_sym 11 10 330 6 8 /home/user/degree-diameter/research/squads/d11D10-r2/A6/d11D10_psl_79_311_orb5_A6_s6.txt psl 79 311

SECS = 330 + 120 as the preamble asks. Seed 6, K = 8. Logs: A6/run_psl71_421_s6.log and A6/run_psl79_311_s6.log. Both exited with
rc = 1, which is haar_sym's normal return when best > 0 and not an error. Gate slots: slot3 (12:50:24 to 12:56:16) and
slot4 (12:50:25 to 12:56:18).

## Results

| run | setup | steps / evals | start raw cost | lowest raw cost (best energy) | final energy | reheats |
|---|---|---|---|---|---|---|
| psl 71 x Z421 | 4.4 s + 9.2 s | 123 / 985 | 30 | 5 (one alpha-orbit, 0 alpha-fixed misses) | 5 | 0 |
| psl 79 x Z311 | 5.6 s + 9.5 s | 131 / 1049 | 57 (energy 120 = 57 + 9 x 7 alpha-fixed misses) | 10 (two alpha-orbits, 0 alpha-fixed misses) | 10 | 0 |

Trajectory of the best raw cost, from the progress lines:
- psl 71: 20 (t = 31 s), 15 (t = 93 s), 5 (t = 221 s), still 5 at t = 314 s and at the end.
- psl 79: 26 (t = 31 s), 25 (t = 61 s), 11 (t = 186 s), 10 (t = 217 s), still 10 at t = 308 s and at the end.

Final energy equals the raw cost in both runs, so ORBW=10 cleared every alpha-fixed miss. The stall is whole alpha-orbits,
not the 1-2 alpha-fixed elements the preamble describes for k = 5 at mu 30-50.

Round 1 reported raw cost 2 on psl 71 x Z421 with ORBW=5. That run used another seed and weight, so it is not reproduced here.
With one seed per group, ORBW=5 and ORBW=10 are not compared.

## Notes for the Opus session

- For a 330 s run to restart at all, REHEATSTEPS must be well below the roughly 125 steps the run makes (about 20), or TMIN must be
  raised above 0.15. Otherwise RESTART=1 does nothing in a short run.
- k = 5 expects mu/k = 5.9 (psl 71) and 7.8 (psl 79) clumps for random S. The anneal reached 1 and 2 clumps, so both runs ended
  one or two orbits short of a solution at this budget.

## Files

- No solution file written (both runs unsolved).
- Logs: /home/user/degree-diameter/research/squads/d11D10-r2/A6/run_psl71_421_s6.log and run_psl79_311_s6.log.
