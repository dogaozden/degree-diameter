# Handoff: job cell-10-5, (Δ, D) = (10, 5)

Branches: claude/d10d5-cell-resume-3e99iw (draft PR #383) and claude/cell-10-5-resume-pahmz5 (same commits).
Sessions: session_01GwxVXqiUsHvTZ9eAfekqhS (Oct 24), session_01NTgHArireuhKVofyqgzKgX (Oct 25 morning, rounds 1-3),
session_01QqmMPMEBdPHeTrrfhst9b1 (Oct 25 afternoon, round 4; this file).

## Best verified result

**4,838** (round 4): the 4,836 graph with one freed flag converted to FLAGDEL (its own flag edge deleted, 3 hubs per
side): research/squads/d10D5/hubs/graphs/d10D5_n4838_flagdel1.{sol,edges.gz,lift2.sol}, check
research/squads/d10D5/hubs/checks/d10D5_n4838_CHECK.md (apsp VALID, rebuilt independently by r4/build_fd.py).
Before: 4,836 (9 freed flags, 36 hubs; d10D5_n4836_CHECK.md). Table 4,000; master has 4,800.

## Where things stand

- 10 freed flags (4,840): two 1-hole states (research/squads/d10D5/r4/k10_orbit_{100,38}.sol). Round 4 threw an exact
  CP-SAT neighbourhood search (r4/lns.py) and 8 Haiku cards at them: every method ends at 1 hole. The hole targets
  lie on no freed line (hub routes cannot help), and every swap that covers the hole breaks >= 9 other targets.
  Treat these 9 flags + a 10th as exhausted.
- FLAGDEL (new, round 4): also delete each freed flag's own edge p-l; 3 hubs per side fit, +2 per converted flag over
  the 9-flag graph (4,838 for one flag, 4,854 for all 9). Explained in research/squads/cells/d10D5.md, section
  "FLAGDEL". The pipeline works up to the last step: single-flag conversions (flags 1, 4, 6) and the 3-flag set
  {1, 6, 4} all reach coverage 0 and D1 0 with a legal hub graph; what remains is the coset-0 endgame (2-8 opposite
  pairs whose geodesics have one nu-parity and no route). The plain annealers (dmfast_fd3, penalty mode) and a
  route-surgery search stall there because nearly every sigma swap breaks coverage or D1.
- The most promising finisher so far: r4/lns2.py, exact CP-SAT on sigma with coverage, D1 AND the coset-0 routes
  (unmixed pairs need sigma(a), sigma(b) concurrent), with FLIPS=1 compound moves (flip a nu on a bad pair's geodesic,
  then repair the ~10-20 newly unmixed pairs exactly). It brings a flip's damage down by 3-5 pairs per round; it had
  not yet closed a state when this file was written.

## Next steps, in order

1. Keep lns2.py (FLIPS=1, more REPAIRS, larger SIZE) running on the best states in r4/runs/ (cF1p21.sol for FDSET
   {1} at 2 bad pairs, cF6a.sol for {6} at 3, cF3b.sol for {1 6 4} at 8); any 0 -> r4/finish_fd.sh then r4/record.sh.
2. Let lns2's neighbourhoods include the points on freed lines and the preimages of lines through freed points (now
   excluded; both ends of one stuck pair, (120, 261), are such points): needs the quadratic coverage/D1 terms.
3. Then convert more flags one at a time (each +2), redoing coverage (fdrun.sh), hubs (hubfix.py) and coset-0.
4. The same hub/FLAGDEL constructions apply unchanged to (11,5), (12,5), (14,5) (W(8), W(9), W(11)).

## How to rebuild and check a FLAGDEL graph

    cd research/squads/d10D5/r4 && gcc -O2 -o gqgen ../../../d10D7/gqgen.c && mkdir -p gq && ./gqgen 7
    python3 build_fd.py gq/gq_q7.bin X.sol "FDSET" x.edges     # independent of dmhub2.c
    gcc -O3 -o apsp ../../../lifts/coordinator_check/apsp.c && ./apsp x.edges 10 5
