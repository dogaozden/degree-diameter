# own-small round 2 cards (16). Shared rules, tools and the ruled-out list: r2/HEADER.md (read it first).

T = /home/user/degree-diameter/research/squads/own-small/tools, GT = /home/user/degree-diameter/research/squads/own-small/runs/gtxt.
Every card: ONE gated job (`$T/slot.sh 900 bash job.sh`) that screens all groups of its orders with short salift_s2
runs (env D as given; e.g. 20-40 CPU s each, two seeds for the best ones), then pushes the best 1-2 (group, seed)
states with START restarts (`START=x.sol.best`) and fresh seeds until the job's time is used. Convert the best state
with best2edges.py and check it with score48. A cost-0 state is a record: check it with score48 at once.

## (3,10): D=10, n = 2pN just above 800 (each card its own (p, N) slot)

- **k1:** p=4, N=101 (n=808, C101) and N=102 (n=816, all 4 groups). Fixed-base 4+4 flift was tried (best 8 at 864); joint annealing never was.
- **k2:** p=5, N=82, 83 (n=820, 830) and N=84 (n=840, 15 groups: non-abelian first).
- **k3:** p=6, N=67 (n=804, C67) and N=68 (n=816, 5 groups).
- **k4:** p=6, N=69, 70 (n=828, 840).
- **k5:** p=7, N=58, 59 (n=812, 826) and N=60 (n=840, 13 groups).
- **k6:** p=8, N=51 (n=816) and N=52 (n=832, 5 groups).
- **k7:** p=9, N=45 (n=810, 2 groups) and N=46 (n=828).
- **k8:** p=10, N=41 (n=820) and N=42 (n=840, 6 groups).
- **k9:** p=11 N=37 (n=814), p=12 N=34 (n=816), p=13 N=31 (n=806), p=14 N=29 (n=812); groups of order < 51 are in GT once
  the director's export of orders 16..50 finishes (file GT/exported3), cyclic groups need no table (write one).
- **k10:** p=5, N=81 (n=810): PUSH. The director screened all 15 groups of order 81 (runs/p5/RANK.txt lists cost per
  group and the saved states runs/p5/s81_<id>_<seed>.sol.best). Take the best 2 groups and push them hard: START restarts
  from the saved states, several fresh seeds, and a few temperature schedules (T0 3..20, T1 0.1..0.5).
- **k11:** p=5, N=81 (n=810): PUSH the 3rd-5th best groups of runs/p5/RANK.txt the same way (do not take k10's two).

## (3,9): D=9, n = 2pN just above 506

- **m1:** p=5 N=51, 52 (n=510, 520) and p=6 N=43, 44 (n=516, 528).
- **m2:** p=8 N=32 (n=512, 51 groups: non-abelian first; screen 10 s each) and p=7 N=37 (n=518).
- **m3:** p=10 N=26 (n=520), p=11 N=24 (n=528), p=12 N=22 (n=528), p=13 N=20 (n=520), p=16 N=16 (n=512).

## Quartic cells: write a degree-4 joint annealer first

- **q1 (4,8) > 2,184:** copy $T/salift_s.c to your folder and make a degree-4 version (base = 4 perfect matchings between
  the p white and p black base vertices, multi-edges allowed, voltages on every edge; same moves and cost; check that
  the cost of a known lift matches flift's). Run at d=4, D=8 with n = 2pN in 2,186..2,300: p=3 N=365..383, p=4 N=274..287,
  p=5 N=219..230, p=6 N=183..191. Groups: you may run GAP inside your gated job for these orders ($T/gap_export.g, write
  into your folder; skip orders with more than 60 groups). Earlier: only fixed 2+2/3+3 bases with metacyclic groups.
  Score: score48 EDGES 4 8 on a lift edge list you write (vertex (u,g) = u*N+g, edge (u,g)~(v,g*a)).
- **q2 (4,9) > 4,970:** the same degree-4 annealer (write your own, do not wait for q1) at d=4, D=9 with n = 2pN in
  4,972..5,100: p=4 N=622..637, p=5 N=498..510, p=6 N=415..425 (GAP inside the gated job, orders with few groups first).
  Score: score48 EDGES 4 9.

## Wildcard

- **w4 (3,10):** find a way to make the joint annealer stronger at n = 804..830 that none of k1-k11 uses (for example a
  move that re-routes a far pair's shortest walks, a tabu list, parallel tempering inside one job, or an exact
  completion of the last voltages), test it on 5+5 over SmallGroup(81,4) from runs/p5/s81_4_*.sol.best, then use it.
