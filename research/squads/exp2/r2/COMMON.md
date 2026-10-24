# exp2-squad round 2: shared brief for every card

## Goal and current bests
Bipartite degree–diameter cells at diameter 7. Score = vertices of a graph with max degree Δ and diameter ≤ 7 that
apsp checks VALID. Bests now (all apsp VALID): **(7,7) 23,462** (13 freed pairs), **(9,7) 117,674** (13 pairs, round-1
card c3), **(11,7) 398,582** (1 pair). Tables: 23,436 / 117,648 / 398,580. Every freed pair adds 2 vertices, so the
task is: more freed pairs K. (7,7) matters most (a pair there is worth 5–17× more of the score than at q = 7, 9).

## Construction (2-minute read: research/squads/exp2/hexd7/README.md)
Three copies of the generalized hexagon H(q) (q = 5, 7, 9 for Δ = 7, 9, 11) plus one extra edge per vertex
(point p, level i ~ line M(p), level i+1). A freed pair deletes the 3 extra edges of a point p and adds 2 hub vertices.
Hubs are linked by a hub graph (file: "K m", then m lines "j k"; hub degrees ≤ q−1). The program re-chooses M so that
every freed point and freed line still reaches everything within 7.

## What round 1 found
- K = 13 (PG(2,3) hubs) solves at q = 5 in ~10 s with the new options and at q = 7 in ~5 min CPU; K = 18 (random hub graph)
  solved at q = 5; K = 24 got to cost 31 (almost) in 900 s; K = 40 (GQ(3,3) hubs) stalls near proxy 4,000–5,000.
- Hubs need a neighbour in each of the 3 levels; 4 copies (Z_4) are hopeless (~390 uncovered per source).

## Setup (inside your card folder)
    R=/home/user/degree-diameter
    gcc -O2 -march=native -o d7hex $R/research/squads/exp2/hexd7/d7hex.c -lm      # current version (new options below)
    gcc -O2 -o hexgen $R/research/p4/d6/hexgen.c && mkdir -p hex && ./hexgen 5    # or 7, 9
    gcc -O2 -o apsp $R/research/lifts/coordinator_check/apsp.c
Shared read-only hub graphs in $R/research/squads/exp2/r2/shared/: pg23.hg (K=13), pg24.hg (K=21), fano.hg (K=7),
gq33.hg (K=40), rnd24.hg (K=24, random), rnd32.hg (K=32, random).

## Running (new options; all are environment variables)
    BESTK=6 SKIPFULL=1 DROP=1 timeout 1500 nice -n 10 ./d7hex search hex/hex_q5.bin 0 SEED 1200 out.sol 3 3 4 HGFILE
    args: HEXBIN K seed maxsec out.sol mode alg mind HGFILE   (mode 3 = hub graph from file, K comes from the file)
    alg 3 = type-2 pre-pass + algebraic covers + fast search (best at q = 5); alg 2 skips the pre-pass (try both at q = 7, 9)
    mind = minimum hexagon distance between freed points (4 or 6)
    BESTK=6     best-of-6 moves (a bit faster)
    SKIPFULL=1  skip the slow internal full check (minutes at q = 7, 9); apsp is the real check anyway
    DROP=1      if unsolved at the end, drop the worst pairs until the rest are fine: a near miss becomes a valid smaller K
    DROPSEC=s DROPSTART=t   after t seconds, drop the worst pair whenever the proxy has not fallen 2% in s seconds
It prints "RESULT ... n=..." and writes out.sol (K may be smaller than the file's K after dropping; n = 6N + 2K).

## Scorer (the only thing that counts)
    ./d7hex edges hex/hex_q5.bin out.sol e.txt && ./apsp e.txt 7 7      # apsp EDGES Δ D: Δ first! (9 for q=7, 11 for q=9)
Score = n printed with "RESULT VALID". q = 9 graphs (~400K vertices) take 10–25 min in apsp; q = 7 about 1–3 min.

## Machine rules (4 cores, 15 GB, shared by about 10 jobs)
- one process at a time, one thread; `timeout ... nice -n 10` in front of anything heavy; ≤ 1.5 GB;
- no git commits; edit nothing outside your card folder research/squads/exp2/r2/<card>/;
- time box about 25 minutes (searches are slow on this shared machine; plan one main run).

## Report
Append ONE JSON line to research/squads/exp2/r2/scoreboard.jsonl:
{"card": "cN", "idea": "<one line>", "code": "<path>", "command": "<exact>", "score": <n or 0>, "valid": true|false,
 "next": "<one line>"}
Keep the .sol and the apsp output in your folder. Reply in at most 5 lines.
