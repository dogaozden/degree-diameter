# Card A3: k = 5 Frobenius anneal, AFROB=2, psl 243 x Z11 (round d11D10-r2)

Outcome: NOT RUN. The job never got a gate slot, so there is no cost trace, no lowest cost and no count of uncovered
alpha-fixed elements. Wrapped up at 13:37 UTC on the coordinator's instruction (no new heavy runs).

## Setup (prepared, never executed)

- Group G = psl 243 x Z11, N = 78,917,652 (157,835,304 vertices if solved). Preamble numbers: lambda = 14.08, mu = 60.6.
- Automorphism: AFROB=2 (Frobenius x -> x^9 on matrix entries, order 5), z -> 3z on Z11 (default AR).
  Fix(alpha) = PSL(2,3) (11 elements) plus e.
- Orbit shape: ORBIT="5 2 1" (S = {e} + two alpha-orbits of size 5, d = 11). ORBW=5. Seed 1 (the card names no seed).
  K = 8. SECONDS = 600. THREADS unset.
- Binary: A3/haar_sym_A3, built 12:50 from A3/haar_sym_A3.c = research/structured/haar_sym.c plus one block (env
  FIXREPORT=1) that runs after the search and prints the raw cost and the uncovered alpha-fixed count (fixmiss) of the
  returned S. The search code is unchanged. Build: `gcc -O3 -march=native -fopenmp -o haar_sym_A3 haar_sym_A3.c -lm`
  (A3/build.log: warnings only).

Command (queued, never started):

    /home/user/degree-diameter/research/squads/d11D10-r2/gate.sh 720 env ORBIT="5 2 1" AFROB=2 ORBW=5 \
      CKPT=/home/user/degree-diameter/research/squads/d11D10-r2/A3/a3.ckpt FIXREPORT=1 \
      /home/user/degree-diameter/research/squads/d11D10-r2/A3/haar_sym_A3 11 10 600 1 8 \
      /home/user/degree-diameter/research/squads/d11D10-r2/A3/d11D10_psl_243_11_orb5_af2_s1.txt psl 243 11 \
      > A3/run.out 2> A3/run.err

## What happened

- 12:50 UTC: the job was launched in the background with a 720 s gate limit. It polls for a free slot every 10 s
  (slots/P = 5).
- Between 12:56 and 13:25 every freed slot was taken at once by another job (cards' RANDORB, BENCH, check and chain
  scripts, and Opus runs: the k = 5 AFROB=3 anneal, the k = 10 random searches, then the k = 10 AR=3 searches). The
  gate has no queue, so the polling job lost every race. slots/usage.log has no `haar_sym_A3` entry.
- About 13:05 UTC: the background job reached its 15-minute background limit and was stopped, still waiting for a slot.
  The progress monitor (task b98zddxs3) ended with exit 144 and never reported a take event.
- run.out and run.err are empty. No checker ran, because there was no solution file.
- Processes at 13:37 UTC: none of mine. The gate job, the monitor loop and haar_sym_A3 are all gone.
- Aside from my card: usage.log shows haarcheck_pq and pqcheck run on opus/d11D10_psl_243_11_orb10_frob1d_ar3_s201.txt
  at 13:24:49 to 13:25:45, both exiting 0. I did not read their output.

## Results

None. The card's numbers (cost every ~2 min, lowest cost, uncovered alpha-fixed count at the end) do not exist.
Scoreboard line: score 0, valid false, best_cost "not run".

## Conclusion

Card A3 says nothing about AFROB=2 with k = 5. Nothing here changes the picture: per the coordinator, the cell was
solved at 157,835,304 by the k = 10 AR=3 search, so A3 is not needed.

Key finding for the coordinator: the gate has no fair queue. With 5 slots and continuous takers, a job that polls
starves for 15 minutes or more. Any card that needs a guaranteed run needs a FIFO queue or a reserved slot.
