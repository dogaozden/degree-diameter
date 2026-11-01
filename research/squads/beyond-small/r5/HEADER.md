# Job beyond-small, squad round 5 — common header

Same setting as round 4: read research/squads/beyond-small/r4/HEADER.md (goal, engine growb, side swap, checking), and
the machine rules / scoreboard format in research/squads/beyond-small/r1/HEADER.md. Your folder: r5/<card>/, scoreboard
research/squads/beyond-small/r5/scoreboard.jsonl. Commands under 100 s each (`timeout 100 nice -n 10`); a long loop may run
in the background **only if you stay with it until it ends** (check it every few minutes) — do not hand back while it runs.

**New start (best so far 35,728 = 33,792 + 22·(43 + 45)):** side A r5/startA.txt (43 orbits, global ids; swapped form
r5/startA_swap.txt for growb on data/Gswap.edges), side B r5/startB.txt (45 orbits). Cap 48 per side.
What worked in round 4 (scripts you may copy into your folder and adapt):
- region destroy (r4/f07/region_destroy.py): drop every orbit whose keys meet a random affine key region, regrow 45 s;
- big destroy (r4/f08/step.sh, r4/f04/step.sh): drop 8–12 orbits, 2 growb seeds, alternate with small drops;
- conflict-directed destroy (r4/f06/blk.c + conflict_lns.sh): drop the orbits that block the most candidate covers;
- random small destroy with long repairs (r4/f05/lns_b.sh); annealing over orbit packings (r3/e03/anneal3.c).
Every accepted state must keep the orbit count ≥ the start. Save improvements as best_side<A|B>_<count>.txt (global ids)
and verify them with research/squads/beyond-small/graphs/build_d17D5_hubs.py (with the other side's start file) + apsp.
Time box 50 min.
