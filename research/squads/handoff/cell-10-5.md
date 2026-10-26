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

## Status at the end of session_01QqmMPMEBdPHeTrrfhst9b1 (Oct 25, ~15:25 PT)

- Best verified: **4,840** (FLAGDEL on flags 1 and 6). Pushed with check files.
- Third conversion {1,6,5} (4,842): coverage + D1 = 0 (state r4/runs/g40_5.sol, H=3 numbering, its hub graph has no
  hub failures); coset-0 138 -> 9 (strict) -> 7 (penalty) -> 4 (second penalty pass: r4/runs/Q5c8.sol). Best-flip
  lns2 from the 4-state ran ~12 minutes at the end without closing (r4/runs/Q5L3.log, Q5L4.log, Q5L1.log; it
  wandered 4-6; the {1,6} case needed 3 lucky flips from 4). To continue: more penalty passes from Q5c8.sol to
  get <= 3 (`./c0run.sh runs/g40_5.sol runs/Q5c8.sol "1 6 5" runs/X SEED 2 10000000 0.12 0.04 0.7`), then
  `FLIPS=1 BESTFLIP=1 KZ=8 REPAIRS=10 python3 lns2.py runs/g40_5.sol <best> "1 6 5" out.sol`, then finish_fd.sh and
  record.sh.
- Other third flags: {1,6,0} stalls at 3 coverage/D1 holes, {1,6,2} at 2 (with hub failures).

## Resume 4 (session_01ThanGg64Z6Jg1KgXK34ssq, Oct 25-26 night; branch claude/d10d5-cell-resume-4-wwdk2k, PR #396)

Read research/squads/cells/d10D5.md "Resume 4" first. Two model fixes matter for every later conversion:
1. Coverage of a converted flag may not use its own deleted edge (coverfd.py; fixed in dmhub2.c, dmfast_fd.c,
   lns2.py, lns3.py). States produced before this fix can carry hidden coverage holes; re-score them with
   r5/score.sh before trusting them.
2. Hub routes: pairs (p_i, u) with u on l_j and a hub edge (line-side hub i ~ point-side hub j), and dually
   (l_i, t) with t through p_j and hub edge (j ~ i), are covered in every sheet; the coset-0 models now treat them
   as routed (lns2, lns3, dmfast_fd.c).
Scorer for any state: research/squads/d10D5/r5/score.sh STATE.sol C0.lift2.sol "FDSET" (true cost; exact BFS at 0).

### State at ~01:10 UTC Oct 26 (resume 4)

- Best verified: still **4,840** (at 01:10; see below: 4,842 at 02:33).
- {1,6,5} (4,842 candidate): one bad pair left, (283, 339), state r4/runs/H5best_c.sol with STATE r5/S5.sol, FDSET
  "1 6 5" (score.sh: SCORE 1 (1, 0, 0); exact BFS: only P283-P339 sheet 3). 283 = freed point of the converted flag 5.
  Exact nu-only flip tree (r4/fliptree, hub-aware copy of card c8's flip.c): no fix with <= 7 flips (complete).
  sigma is nearly frozen: single swaps that would route a newly unmixed pair cost +2..+29 in coverage/D1 (measured);
  hub rewires do not repair that damage.
- Fresh pipelines with the corrected, hub-aware tools (r4/fresh.sh) started for {1,6,5} (FR5) and {1,6,7} (FR7).

### Next steps (from resume 4)

1. The third conversion is stuck on the converted flag's own freed vertices ("hard core": their pairs have 7 geodesics
   and no route, so only nu can mix them). Best state: {1,6,5} with one bad pair (r4/runs/H5best_c.sol + r5/S5.sol).
   It is exactly isolated for nu (no fix with <= 8 flips; no fix inside a 600-flag SAT ball) and sigma is rigid.
   More of the same compute has low odds; fresh basins (r4/fresh.sh, then r4/alt.sh) are the cheapest retry.
2. Most promising new lead: delete an ORDINARY flag edge (x, L) far from the freed flags and add one hub per fibre
   (+2, no hard core; r4/edgedel.py measures the damage: ~73 coset-1/2 pairs of three D1-type families, ~3 coset-0
   pairs). Needs: the three D1-type families as a function like d1.py, in lns2/lns3 step() and in dmhub2.c's
   coverage annealing (fdrun), plus the extra deleted flag in the coset-0 tables (lns3 ISDEL/dele, dmfast delf).
3. Ruled out this session: symmetric (order-8 equivariant) conversions (no equivariant sigma exists), hub rewires as
   repair moves, WalkSAT/reheating/ejection chains/best-flip temperatures (squad round 5, r5/scoreboard.jsonl).
4. Lessons for every tool here: score states with r5/score.sh (true cost); never trust a pipeline "coverage 0"
   produced before the coverage fix; kill processes by PID, never with pkill -f (it can match your own shell).

### 4,842 (02:33 UTC Oct 26)

- **(10,5) >= 4,842**, apsp VALID: research/squads/d10D5/hubs/checks/d10D5_n4842_CHECK.md, graph files
  hubs/graphs/d10D5_n4842_flagdel3.{sol,edges.gz,lift2.sol} (FDSET "1 6 5").
- Recipe that worked: r4/fresh.sh (BASE=... for another base) -> lns3 FOCUS (FW=4, FT=0.6-1.0) -> lns2 for D1 leftovers
  -> r4/tabu.sh (cumulative HARDPAIR walk) from a 1-2 pair state. Several fresh basins are needed: FR5 stalled at 12,
  S5 at 1 (its last pair on the converted flag's own freed point is nu-only and exactly isolated), FR5b closed.
- Fourth conversion from 4,842 started at 02:33: {1,6,5,4}, {1,6,5,7}, {1,6,5,0} (runs/G4_*).
- 03:10 UTC: flags 4, 7, 0 as fourth conversion leave the crowded point 65 with a coverage hole (not closable);
  flag 2 is clean: {1,6,5,2} basins G4_2 (14 coset-0 after two passes) and G4_2b (115 after coverage), tabu walkers
  TB11/TB12 running from G4_2 (r4/runs/G4_2_f.sol + runs/G4_2_c0b.sol). To resume:
  `./tabu.sh runs/G4_2_f.sol runs/G4_2_c0b.sol "1 6 5 2" "" TBx SEED 20` from r4/ (needs BASE graph 4,842).
