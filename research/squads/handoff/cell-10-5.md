# Handoff: job cell-10-5, (Δ, D) = (10, 5)

Branches: claude/d10d5-cell-resume-3e99iw (draft PR #383) and claude/cell-10-5-resume-pahmz5 (same commits).
Sessions: session_01GwxVXqiUsHvTZ9eAfekqhS (Oct 24), session_01NTgHArireuhKVofyqgzKgX (Oct 25 morning, rounds 1-3),
session_01QqmMPMEBdPHeTrrfhst9b1 (Oct 25 afternoon, round 4; this file).

## Best verified result

**4,840** (round 4): the 4,836 graph with two freed flags (41:289 and 398:292) converted to FLAGDEL (own flag edge
deleted, 3 hubs per side): research/squads/d10D5/hubs/graphs/d10D5_n4840_flagdel2.{sol,edges.gz,lift2.sol}, check
research/squads/d10D5/hubs/checks/d10D5_n4840_CHECK.md (apsp VALID, rebuilt independently by r4/build_fd.py).
Before: 4,838 (one FLAGDEL flag, d10D5_n4838_CHECK.md), 4,836 (9 freed flags, 36 hubs). Table 4,000; master 4,800.

## Where things stand

- 10 freed flags with 2 hubs per side (also 4,840): two 1-hole states (r4/k10_orbit_{100,38}.sol). Round 4 threw an
  exact CP-SAT neighbourhood search (r4/lns.py) and 8 Haiku cards at them: every method ends at 1 hole (the hole
  targets lie on no freed line; every swap covering the hole breaks >= 9 targets). Treat as exhausted.
- FLAGDEL (round 4): delete a freed flag's own edge p-l as well; 3 hubs per side fit, +2 per converted flag (4,854 if
  all 9 convert). research/squads/cells/d10D5.md, section "FLAGDEL". Two flags converted (4,840). Pipeline per extra
  flag, from the last valid state (all in r4/): mkhubF.py -> fdrun.sh (coverage + D1) -> lns2.py NOC0=1 (exact
  coverage + D1 when the annealer stalls at 1-4 holes) -> hubfix.py -> c0run.sh RELAX=1 (strict, ~12M its) then
  RELAX=2 (penalty), repeat until <= 4 -> lns2.py FLIPS=1 BESTFLIP=1 KZ=8 REPAIRS=10 -> finish_fd.sh -> record.sh.
  One conversion took ~40 minutes on 4 cores.
- Third conversion (4,842): started at the end of this session from the 4,840 state with {1,6,5} and {1,6,0}
  (status at the end of this file).

## Next steps, in order

1. Third, fourth, ... conversions from the newest valid state (pipeline above). Flags 5 and 0 next; 4, 7 and 8 stalled
   at 1-2 coverage holes as second flags (try them later, or with larger lns2 neighbourhoods).
2. The coset-0 endgame is the slow part: drive dmfast_fd3 as low as possible first (several passes), then lns2.
   lns2's flip scorer could count only the newly unmixed pairs that cannot be rerouted (WSCORE=1 does a crude version).
3. The same hub/FLAGDEL constructions apply unchanged to (11,5), (12,5), (14,5) (W(8), W(9), W(11)); spare hub degree
   there is q+3-6 per hub.

## How to rebuild and check a FLAGDEL graph

    cd research/squads/d10D5/r4 && gcc -O2 -o gqgen ../../../d10D7/gqgen.c && mkdir -p gq && ./gqgen 7
    python3 build_fd.py gq/gq_q7.bin X.sol "FDSET" x.edges     # independent of dmhub2.c
    gcc -O3 -o apsp ../../../lifts/coordinator_check/apsp.c && ./apsp x.edges 10 5
