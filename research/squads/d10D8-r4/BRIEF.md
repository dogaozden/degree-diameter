# Squad round d10D8-r4 (cell-10-8 session, 2026-10-25): shared brief, read this first

GOAL: beat the bipartite (Δ, D) = (10, 8) record 1,176,480 vertices. Our route: a Haar graph H(G, S) with |S| = 10 on a
group of order N ≥ 588,241 whose diameter is ≤ 8. The searcher is `research/d10D8/sym2/haar_sym2.c` (C, ~1400 lines):
S = {e} ∪ O1 ∪ O2 ∪ O3, each Oj an orbit {x, α(x), α²(x)} of an automorphism α of order 3 ("ORBIT=\"3 3 1\"").
The cost of S = number of group elements NOT reachable by an alternating word s1 s2⁻¹ s3 … of length ≤ 7 (cost 0 = a
valid graph = a new record). Main group: `prod psl 7 sl 8 7` = PSL(2,7) × SL(2,8) × Z7, N = 592,704 (2N = 1,185,408).
Second group: `psl 23 97`, N = 588,984.

What we know (from 4 runs of simulated annealing over orbit choices):
- A "descent" (anneal from fresh random orbits until it stalls) ends at cost 10–24, median 17–18, in 30–100 s;
  the best ever found is cost 7. Nobody has reached 0. Costs are mostly multiples of 3 (uncovered α-orbits), plus
  uncovered α-fixed elements (26 of them, each counts 1).
- Good states are isolated: from the cost-7 state, ALL ~197,000 single-orbit replacements cost ≥ 8 (most ≥ 24).
- Re-annealing from a good state (reheat) sometimes finds a better one (19 → 7, 18 → 10, 18 → 9), often returns to the
  same state.
- Step anatomy (orbit_main, around line 1102): each step picks one orbit slot j, makes K = 8 candidate orbits (70 %
  "targeted": targeted() at line 756 builds a new letter that makes one currently uncovered element reachable, via
  two random walks of the other letters), evaluates all 8 with cost_any() (early abort once worse than the best so far),
  and accepts the best by Metropolis at temperature T (in orbit units = cost/3), line 1140. T cools from TMAX = 1.5 with
  half-life COOL seconds to TMIN = 0.15; after REHEAT s without improving the chain's best the chain is reheated
  (line 1150). With RESTARTAFTER=0 every stall starts a fresh chain and prints
  `CHAIN n min <cost> secs <s> evals <e> S <10 element indices>` to stderr.

Build (from your card folder; copy the source first if you modify it, never edit research/d10D8/):
  cp /home/user/degree-diameter/research/d10D8/sym2/haar_sym2.c my.c   # then edit my.c
  gcc -O3 -march=native -fopenmp -o my my.c -lm
Standard test (THE SCORER for search-heuristic cards; about 8 minutes, one process):
  ORBIT="3 3 1" RESTARTAFTER=0 COOL=15 REHEAT=30 timeout 500 nice -n 10 ./my 10 8 480 <seed> 8 /dev/null prod psl 7 sl 8 7 2> run.log
  then: grep CHAIN run.log | awk '{print $4}' | sort -n | tr '\n' ' '     (the chain minima)
Baseline (unmodified code, same settings, on a busy machine): 15 chains in 12 min, minima
  12 12 13 13 15 15 16 17 18 21 21 21 21 22 24 (median 17, best 12). A heuristic that clearly lowers the median or
  produces cost ≤ 9 more often is a win. Report the sorted minima and the number of chains.
If ANY run prints "full diameter check: OK" or a RESULT line with best=0, stop and say so in the first line of your reply
(write the output file to your folder instead of /dev/null if you can).

MACHINE RULES (4 cores shared with 4 main searches): ONE heavy process at a time, always `timeout ... nice -n 10`,
THREADS unset (1), at most 2 standard tests (16 CPU-minutes) per card unless your card says otherwise. No git commits.
Write only inside your card folder research/squads/d10D8-r4/<card>/. Time box: about 25 minutes.

REPORT: append ONE line of JSON to research/squads/d10D8-r4/scoreboard.jsonl:
{"card": "c<N>", "idea": "<one line>", "code": "<path>", "command": "<exact>", "score": <median chain minimum, or your
card's stated score>, "valid": true|false, "next": "<one line>", "minima": "<sorted chain minima if any>"}
and reply in at most 5 lines.
