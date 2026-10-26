# own-small round 2 cards (16). Shared rules, tools and the ruled-out list: r2/HEADER.md (read it first).

T = /home/user/degree-diameter/research/squads/own-small/tools, GT = /home/user/degree-diameter/research/squads/own-small/runs/gtxt.
Every card: ONE gated job (`$T/slot.sh 900 bash job.sh`) that screens all groups of its orders with short salift_s2
runs (env D as given; e.g. 20-40 CPU s each, two seeds for the best ones), then pushes the best 1-2 (group, seed)
states with START restarts (`START=x.sol.best`) and fresh seeds until the job's time is used. Convert the best state
with best2edges.py and check it with score48. A cost-0 state is a record: check it with score48 at once.

## (3,10): D=10, goal n > 810 (record now 810); each card climbs in group order inside its own (p, N) slot

- **k1:** p=4, N=102..110 (n=816..880).
- **k2:** p=5, N=82..86 (n=820..860).
- **k3:** p=5, N=87..92 (n=870..920).
- **k4:** p=6, N=68..72 (n=816..864).
- **k5:** p=6, N=73..80 (n=876..960).
- **k6:** p=7, N=58..63 (n=812..882).
- **k7:** p=8, N=51..56 (n=816..896).
- **k8:** p=9, N=45..50 (n=810..900).
- **k9:** p=10 N=41..45 (n=820..900), p=11 N=37..40, p=12 N=34..37, p=13 N=31..34 (groups of order < 51 are in GT too).
- **k10:** prime-power groups, since both 810 winners are 3-groups: N=64 with p=7 (n=896; 267 groups, sample 40 with a
  small abelianisation, i.e. few generators) and N=125 with p=4 (n=1,000; 5 groups).
- **k11:** the largest n: p=5 N=96..100 (n=960..1,000; order 96 has 231 groups, sample 40) and p=6 N=82..84 (n=984..1,008).

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
  completion of the last voltages), test it on 5+5 over SmallGroup(81,4) (plain salift stalls at cost 2-8 there; state runs/p5/s81_4_1.sol.best), then
  use it to reach n > 810.
