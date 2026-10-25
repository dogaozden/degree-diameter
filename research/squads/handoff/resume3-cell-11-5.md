# Handoff: job resume3-cell-11-5 (round 3 of cell-11-5), Oct 25 2026

Session session_018TRrddhVEdN311drmbPpBK, branch claude/cell-11-5-bipartite-search-lyemfs (continues the round-2
branch; draft PR #388).

## Result
- **(11,5) ≥ 7,032** (was 7,020): DM Z6 lift of W(8) plus one point-line pair. research/d11D5/graphs/d11D5_n7032_CHECK.md
  (apsp.c VALID, diameter exactly 5, 11-regular, bipartite, 38,676 edges, sha256 4355f145...). Needs the coordinator's check.

## How (the pipeline that works)
1. Base with n > 585: W(8) + a point-line switch (research/d11D5/inc/mkinc.py, addpair.py, w8r/genk.py).
2. Structural cost (research/d11D5/plus/plusopt7.c, exact, 4 ms) to <= ~20 by po7 annealing (T0 20 -> 0.4), then to 0
   with the clause-weighting search wpo (research/squads/r3-d11D5/c2/wpo.c). wpo is strong from low cost and drifts
   upward from cost in the hundreds. Annealing, tabu, LNS, tempering and exhaustive 2-moves all stop at 2 at n = 586.
3. Flag cocycle nu: research/d11D5/inc/nujoint.c annealing, then SIGFIX=1 FIRST=1 (greedy sigma swaps that give a
   violated pair a sigma route), then TARGET=1 annealing (those swaps as moves, PS = 0.02). From 2 violated pairs
   TARGET reached 0 in 670 moves; plain annealing stalls at 5-30.
4. Check: research/d11D5/inc/finish.sh (z6lift exact lift cost, edge list, apsp.c).

## Open (in order)
(see the end of this file, filled at the stop)
