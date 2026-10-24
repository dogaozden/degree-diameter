# exp2-squad round 1: shared brief for every card

## Goal
Raise the bipartite degree–diameter cells at diameter D = 7: (Δ,D) = (7,7), (9,7), (11,7). Score = number of
vertices of a graph with max degree Δ and diameter ≤ 7, checked VALID by the all-pairs checker. Current bests of
this session: (7,7) **23,462**, (9,7) 117,650, (11,7) 398,582 (table values 23,436 / 117,648 / 398,580).

## The construction you are working with (read research/squads/exp2/hexd7/README.md, 2 minutes)
- H(q) = generalized hexagon (q = 5, 7, 9 for Δ = 7, 9, 11): N points, N lines, each point on q+1 lines.
- X = three copies of H(q) (levels 0,1,2) plus one extra edge per vertex: point p at level i ~ line M(p) at
  level i+1, for a bijection M: points -> lines. Max degree q+2, diameter 7 for ANY M. 6N vertices = table value.
- Freed pair: delete the 3 extra edges of a point p and add 2 new "hub" vertices: z ~ (p,0),(p,1),(p,2) and
  z' ~ (M(p),0),(M(p),1),(M(p),2). +2 vertices per pair. M must then be re-chosen near p so that p still reaches
  everything; the program d7hex does that (algebraic cover + fast local search).
- Hubs of the same side must be within distance 6 of each other. We link them with a "hub graph": edges between
  line-side hub j and point-side hub k, at most q−1 per hub (spare degree). Built in: PG(2,q−2) (mode 2). Any
  bipartite hub graph with max degree ≤ q−1 in which same-side hubs are within distance 6 works (mode 3, from a file:
  first line "K m", then m lines "j k", 0 ≤ j,k < K; K = number of freed pairs).

## Setup (inside your card folder; nothing is shared except read-only inputs)
    R=/home/user/degree-diameter
    gcc -O2 -march=native -o d7hex $R/research/squads/exp2/hexd7/d7hex.c -lm
    gcc -O2 -o hexgen $R/research/p4/d6/hexgen.c && mkdir -p hex && ./hexgen 5     # writes hex/hex_q5.bin (also 7, 9)
    gcc -O2 -o apsp $R/research/lifts/coordinator_check/apsp.c
Read-only inputs: $R/research/squads/exp2/r1/shared/ (pg23.hg = PG(2,3) hub graph with K = 13; q5_K13_pg23.sol =
a valid (7,7) solution on 23,462 vertices).

Run a search (example: q = 5, hub graph from file, fast search):
    timeout 900 nice -n 10 ./d7hex search hex/hex_q5.bin 0 SEED 600 out.sol 3 2 4 $R/research/squads/exp2/r1/shared/pg23.hg
    (args: HEXBIN K seed maxsec out.sol mode alg mind HGFILE; with mode 3, K comes from the file; mind = minimum
    hexagon distance between freed points, 2/4/6)
It prints "RESULT ... VALID" or "unsolved". The vertex count is n = 6N + 2K.

## Scorer (the only thing that counts)
    ./d7hex edges hex/hex_q5.bin out.sol e.txt && ./apsp e.txt 7 7      # Δ = 7; use 9 for q=7, 11 for q=9
A score is the n printed by apsp with "RESULT VALID". If you build a graph some other way, write an edge list
("n" on the first line, then "u v" per edge, vertices 0..n-1) and run apsp on it.
q = 9 graphs have ~400K vertices: apsp takes ~10 min; only run it on a solution you want scored.

## Machine rules (4 cores and 15 GB shared by 9 agents)
- one thread; `timeout 900 nice -n 10` in front of anything heavy; at most ~1.5 GB of memory;
- no git commits; do not edit files outside your own card folder research/squads/exp2/r1/<card>/;
- total time box about 15–20 minutes.

## Report
Append ONE line of JSON to research/squads/exp2/r1/scoreboard.jsonl:
{"card": "cN", "idea": "<one line>", "code": "<path>", "command": "<exact>", "score": <n or 0>, "valid": true|false,
 "next": "<one line>"}
Keep valid solution files (.sol and the apsp output) in your folder. Reply to the caller in at most 5 lines.
