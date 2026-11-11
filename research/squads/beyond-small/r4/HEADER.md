# Job beyond-small, squad round 4 — common header (read this first, then your card)

Machine rules, scorer and scoreboard format: as in research/squads/beyond-small/r1/HEADER.md ("Machine rules", "Scorer",
"Scoreboard"). Your folder: research/squads/beyond-small/r4/<card>/, scoreboard research/squads/beyond-small/r4/scoreboard.jsonl.
Every command under 100 s (`timeout 100 nice -n 10`), one thread. The box is loaded; that is expected.

## Goal: more Z22-orbits of hubs on ONE side of the (16,5) graph G

Best so far: **35,420+** = G (33,792) + 36 orbits on side A + 39 orbits on side B (22 hubs per orbit). Background: read
research/frontier/beyond/BEYOND_SMALL.md, section "(17,5): hubs on the (16,5) route-chart graph" (the proposition, keys,
orbits). The two sides are independent, so every card works on one side only and the director combines the best sides.
Each extra orbit is +22 vertices; the cap is 48 orbits per side (768 keys / 16).

Engine: research/squads/beyond-small/r3/e02/growb.c (read its header). `growb EDGES FIXED OUT SECS SEED [KD] [R]` grows
"B-orbits" (bases N ⊆ the A side, global ids < 16896) from the fixed list FIXED and writes all of them (fixed + new) to OUT.
- Side B: EDGES = research/squads/beyond-small/data/d16D5_n33792.edges, start = r4/startB.txt (39 orbits).
- Side A: run growb on the side-swapped graph EDGES = research/squads/beyond-small/data/Gswap.edges (vertex v ↦ v ± 16896),
  start = r4/startA_swap.txt (36 orbits, swapped ids). Convert back by adding 16896 to every id (r4/startA.txt is that form).
- The director's destroy-and-repair loop (research/squads/beyond-small/director/growA/lns.sh) drops 2–5 random orbits,
  regrows 60 s and keeps the result if it has at least as many orbits; it took A 33 → 36 and B 37 → 39.

Check a result: `python3 research/squads/beyond-small/graphs/build_d17D5_hubs.py OUT.edges --orbits A_GLOBAL.txt B.txt`
(checks cover and compatibility itself) then `research/squads/beyond-small/bin/apsp OUT.edges 17 5`. Score = largest
VALID n you can build with the other side taken from r4/startA.txt or r4/startB.txt. Save your side's orbit file as
`best_side<A|B>_<count>.txt` (global ids) in your folder and give its path in the scoreboard line.
