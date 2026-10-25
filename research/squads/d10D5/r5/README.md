# d10D5 squad round 5: close the coset-0 endgame of a third FLAGDEL conversion (4,842)

Cell (10,5). Verified record 4,840 (research/squads/d10D5/hubs/checks/d10D5_n4840_CHECK.md). Background: research/squads/cells/d10D5.md,
sections "The construction" and "FLAGDEL". Machine: 4 cores, 15 GB, shared by Opus and 8 cards.

## The problem in one paragraph

The graph is a Z6 lift of the incidence graph of W(7) (400 points, 400 lines) with a doubled matching sigma (point -> line)
and flag voltages nu in {0,3} (written 0/3 in the lift2 file, 0/1 in the code), plus hubs at 9 "freed" flags. A third
flag converted to FLAGDEL (its own edge deleted, +2 vertices) gives 4,842. All conditions except one ("coset-0") are
already satisfied in the start states. Coset-0: for every opposite pair (two points at distance 4, or two lines), the
8 geodesics (7 if one uses a deleted flag edge) must NOT all have the same nu-parity ("mixed"), OR the pair has a route
(points a, b: sigma(a) and sigma(b) meet, both a and b non-freed; lines s, t: sinv(s), sinv(t) collinear, both
non-freed). Pairs with a freed endpoint can only be fixed by nu. Moves: flip one nu (a flag lies on 1,372 geodesics;
a flip typically newly unmixes 3-9 unrouted pairs), or change sigma (swap two points' lines), which changes routes and
must keep coverage and D1 at 0 (the scorer counts them).

## Start states (in this folder)

| state | FDSET | score | note |
|---|---|---|---|
| S5.sol + S5_c0.lift2.sol | "1 6 5" | 4 (4 coset-0) | deep local minimum: in every exact neighbourhood tried, fixing a bad pair costs >= 2 elsewhere |
| S4.sol + S4_c0.lift2.sol | "1 6 4" | 10 | after three dmfast passes |
| K4.sol + V4840.lift2.sol | "1 6 4" | 31 (12 coset-0, 19 D1) | the valid 4,840 sigma/nu with flag 4 just converted (no annealing yet) |
| K5.sol + V4840.lift2.sol | "1 6 5" | 39 (10, 7 coverage, 22 D1) | same for flag 5 |

The .sol (dmhub format: free / sigma / hubgraph ...) is the STATE (freed points, hub graph); the .lift2.sol holds the
sigma and nu that count (line 3 = sigma, last line = 3*nu for the 3,200 flags). Output of every tool is a lift2.sol.

## Scorer (the only judge)

    /home/user/degree-diameter/research/squads/d10D5/r5/score.sh STATE.sol C0.lift2.sol "FDSET"

prints `SCORE n (coset0, coverage, D1)`; at n = 0 it runs the exact BFS check and prints `RESULT VALID d=10 D=5 n=4842`
on success. Lower is better. A card wins with SCORE 0 + RESULT VALID.

## Tools (in ../r4/; copy into your card folder before changing anything; run from ../r4/ or copy gq/, lns.py etc.)

- `c0run.sh STATE C0 "FDSET" OUTPREFIX SEED RELAX ITERS TEMP0 [SWAPP PTARG]`: simulated annealing of nu and sigma
  (dmfast_fd3, C, fast). RELAX=2 = penalty mode (coverage/D1 may break at a cost). Writes OUTPREFIX.sol (lift2).
  Example: `./c0run.sh ../r5/S5.sol ../r5/S5_c0.lift2.sol "1 6 5" ../r5/c2/a 7 2 10000000 0.12 0.04 0.7` (~5 min).
  Source dmfast_fd.c: exact incremental flip_delta(f), PTARG = probability of flipping a flag on a bad pair's geodesic.
- `lns2.py STATE C0 "FDSET" OUT`: exact CP-SAT neighbourhood search on sigma (nu fixed); env SECS STEP SIZE KZ SEED;
  FLIPS=1 BESTFLIP=1 REPAIRS=8: flip the least damaging flag on a bad pair, then repair by CP-SAT (this closed 4 -> 0
  for the second conversion).
- `lns3.py STATE C0 "FDSET" OUT`: CP-SAT with sigma AND nu variable; FOCUS=1 picks one bad pair and its flags;
  env NPHI SIZE STEP KZ FW (weight of the focused pair) FT (temperature for uphill moves) CHEAP=1 (prefer flags whose
  flip unmixes few unrouted pairs). Python API pieces: PF/LF geodesic flag tables, unm_vec, crit(f, ...).
- `rewire.py`, `coverfd.py` (corrected coverage), `d1.py`, `failpairs.py X.edges` (lists pairs at distance > 5 of a
  built graph), `finish_fd.sh` (exact check).

## Card rules

THREADS=1 / WORKERS=1, `timeout 1500 nice -n 10` on every heavy command, at most ONE heavy process of yours at a time,
< 1.5 GB memory, time box ~25 minutes in total. Work only in `r5/<card>/` (create it). No git. Never edit files in
r4/ or r5/ outside your card folder. Append ONE JSON line to `r5/scoreboard.jsonl`:
{"card", "idea", "code", "command", "score" (best SCORE n reached), "state" (path of your best lift2.sol and the
STATE .sol and FDSET it goes with), "valid" (true only if score.sh printed RESULT VALID), "next"} and reply in at
most 5 lines. If you reach SCORE 0, run score.sh at once (it does the exact check) and put the paths in the line.
