# c7 notes (surgery and local search on whole graphs)

Files: sa.c (simulated annealing over 2-switches, cost = far pairs), ft.c (focused tabu: guided 2-switches that
pull a far pair (x,y) closer, candidates scored by full recomputation), h684.edges (684 Haar graph C6 x (C19:C3),
rebuilt with mcos "1|1" on SmallGroup(342,12); check.sh gives bad=0).

Cost evaluation: bit-parallel levels (5 iterations over adjacency), ~0.15 ms per eval at n=686.

Results so far:
- 684 Haar graph rebuilt: bad 0 (verified).
- 686 = 684 + one vertex pair (5 edges removed, 11 added): start cost 283-303. SA (T 3->0.3, 600k moves): best 268.
  SA (T 2->0.05, 20k): 258.
- Calibration SA from random 6-regular bipartite: n=300 solved in 7 s, n=400 in 27 s, n=500 stalls at 142 after 1M moves.
