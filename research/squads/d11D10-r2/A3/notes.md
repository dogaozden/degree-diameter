# Card A3: k = 5 Frobenius anneal, AFROB=2, psl 243 x Z11 (round d11D10-r2)

Status: run queued at the gate (launched 12:50 UTC, waiting for a free slot). Numbers below are filled in after the run.

## Setup

- Group G = psl 243 x Z11, N = 78,917,652 (157,835,304 vertices if a solution is found). Preamble numbers: lambda = 14.08, mu = 60.6.
- Automorphism: AFROB=2 (Frobenius x -> x^9 on the matrix entries, order 5), z -> 3z on Z11 (default AR).
  Fix(alpha) = PSL(2,3) (11 elements) plus e.
- Orbit shape: ORBIT="5 2 1" (S = {e} + two alpha-orbits of size 5; d = 11).
- Cost weight ORBW=5 (an uncovered alpha-fixed element weighs 5 in the annealing energy).
- Seed 1 (the card names no seed); K = 8 candidates per move; SECONDS = 600; THREADS unset (1).
- Binary: A3/haar_sym_A3, a copy of research/structured/haar_sym.c with one extra block (env FIXREPORT=1) that runs
  after the search and before the RESULT line. It prints the raw cost and the number of uncovered alpha-fixed
  elements (fixmiss) of the returned S. The search code is unchanged. Build: `gcc -O3 -march=native -fopenmp -o
  haar_sym_A3 haar_sym_A3.c -lm` (build.log: warnings only).

## Command

    /home/user/degree-diameter/research/squads/d11D10-r2/gate.sh 720 env ORBIT="5 2 1" AFROB=2 ORBW=5 \
      CKPT=/home/user/degree-diameter/research/squads/d11D10-r2/A3/a3.ckpt FIXREPORT=1 \
      /home/user/degree-diameter/research/squads/d11D10-r2/A3/haar_sym_A3 11 10 600 1 8 \
      /home/user/degree-diameter/research/squads/d11D10-r2/A3/d11D10_psl_243_11_orb5_af2_s1.txt psl 243 11 \
      > A3/run.out 2> A3/run.err

Logs: A3/run.out (RESULT and FIXREPORT lines), A3/run.err (progress lines every 30 s), A3/a3.ckpt (best S so far).

## Results

Pending.

## Conclusion

Pending.
