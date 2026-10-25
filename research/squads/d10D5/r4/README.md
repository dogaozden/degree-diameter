# d10D5 squad round 4 (cell (10,5); record 4,836 = 9 freed flags, verified)

Goal: **10 freed flags, a VALID 4,840-vertex graph** (then 11 flags, 4,844). Background: research/squads/cells/d10D5.md
(read "The construction", "Limits") and r3/README.md. Machine: 4 cores, 15 GB shared by Opus and 8 cards.

## State

- 9 flags VALID (4,836): `r4/k9_valid.sol` (dmhub format: free / sigma / mv0 / mv1 / nu / hubgraph).
- 10 flags, coverage cost 1: `r4/k10_orbit_100.sol` (hole: freed point 65 = flag index 3, opposite point 69) and
  `r4/k10_orbit_38.sol` (hole 65 -> 229). Point 65 is "crowded": collinear with three other freed points.
- Round 3: every single sigma swap that covers the hole costs >= 5; tabu, beam, annealing all stay at 1.

## Tools in r4/ (all run from r4/; copy into your card folder before changing them)

- `lns.py` (Opus, round 4): exact CP-SAT large-neighbourhood search on sigma with the flags and hub graph fixed.
  `cover(F, sig, hubadj, listing=True)` is an exact mirror of dmhub.c cover_cost (returns cost, list of holes
  (flag index, 0 = point side / 1 = line side, target)). `lns_step(F, sig, hubadj, S, secs, seed, workers)` frees the
  points in S (their current lines are permuted among them), returns the best new sigma and (model holes, ...).
  The model is exact (routes with two variable assignments are AND terms). Points that are preimages of lines through
  freed points, or lie on freed lines, make the model quadratic: `neighbourhood()` allows at most KZ of them.
  CLI: `SECS=600 STEP=30 SIZE=80 KZ=4 WORKERS=1 SEED=1 python3 lns.py IN.sol OUTPREFIX` (writes OUTPREFIX.sol on
  improvement, OUTPREFIX.final.sol at the end). Each 80-point neighbourhood solves to optimality in 1-5 s; on the
  1-hole states every neighbourhood tried so far is proven optimal at 1.
  Python API: `import sys; sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D5/r4'); import lns`
  then `S = lns.read_sol(path)` gives S['F'] (freed points), S['sig'] (numpy sigma), S['hubadj'] (k x k bool:
  point-side hub of flag i ~ line-side hub of flag j), and `lns.write_sol(path, S, sig, cost)` writes a state.
- `dmhub` (joint annealing of sigma and the hub graph against coverage, then exact BFS cost):
  `FREE="$(awk '$1=="free"{$1="";print}' X.sol)" HGFIRST=1 HGDIST=1 HGFILL=1 PHUB=0.1 HW=2 COVIT=999999999 CSECS=180
  CT0=0.25 ITERS=0 SEED=1 ./dmhub gq/gq_q7.bin X_l2.sol OUT` (X_l2.sol from `python3 ../hubs/sol2lift2.py X.sol
  X_l2.sol`; add `HUBG_IN=X.sol` to start from X's hub graph; `FORCE="p:l"` makes p a flag by a swap; `SHOWUNC=1`
  lists holes). Prints "cover cost final N"; writes OUT.sol (dmhub format, readable by lns.py).
- `finish.sh X.sol OUT [SEED]`: for a coverage-0 state, runs coset-0 (dmfast_hub), the exact dmhub cost and apsp.
  Success = the last line `RESULT VALID d=10 D=5 n=4840` (n = 4800 + 4k). Takes 1-10 minutes. This is the scorer.
- A new flag (p, l) must have p on l (a flag of W(7)), p not freed, l not a freed line. `lns.PTS[l]` = points of line
  l, `lns.LOF[p]` = lines through p, `lns.PM` / `lns.LM` collinearity / concurrency (bool 400x400, no diagonal).

## Card rules

THREADS=1 / WORKERS=1, `timeout 900 nice -n 10` on every heavy command, at most ONE heavy process of yours at a time,
< 1.5 GB memory, time box ~25 minutes in total. Work only in `r4/<card>/` (create it). No git. Append ONE JSON line to
`r4/scoreboard.jsonl`: {"card", "idea", "code", "command", "score" (best 10-flag coverage cost reached, or the VALID n),
"valid", "next"} and reply in at most 5 lines. If you reach coverage 0 with 10+ flags, run finish.sh on it at once and
put the .sol path in the scoreboard line.
