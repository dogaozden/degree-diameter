# own-small round 3 cards (16). Rules and the queue: r3/HEADER.md (read it first).

S = /home/user/degree-diameter/research/squads/own-small. Every card submits at most 14 queue tasks (secs <= 90), in
batches, evolving from its results (restart from good states with START, move to neighbouring groups/orders). Goal per
card: the largest n with a VALID graph in its slot; if one is valid, move up in n.

## (3,11), D = 11, beat 1,260 (ours)
- **x1:** p=6, N=106..112 (n=1,272..1,344), all groups of each order from $S/runs/gtxt (non-abelian first).
- **x2:** p=7, N=91..96 (n=1,274..1,344).
- **x3:** p=8, N=79..84 (n=1,264..1,344); order 81 (3-groups) reached cost 2 at n=1,296 (state $S/runs/d11/s81_p8_5.sol.best,
  group 5 of $S/runs/gtxt/g81.txt; it is a local minimum: use other seeds and other groups of order 81 too).
- **x4:** p=5, N=127..135 (n=1,270..1,350): cyclic tables in $S/runs/cyc; export the others with GAP (orders with <= 30 groups).
- **x5:** p=9 N=70..75 and p=10 N=63..68 (n=1,260..1,360).
- **x6:** p=4, N=158..165 (n=1,264..1,320): export with GAP (skip orders with > 30 groups), cyclic ones from $S/runs/cyc.

## (3,12), D = 12, beat 2,304 (Foster census graph CSS(2304,5); lab 1,320)
- **y1:** p=6, N=193..200 (n=2,316..2,400): cyclic from $S/runs/cyc, others by GAP export (<= 30 groups).
- **y2:** p=7, N=165..172 (n=2,310..2,408).
- **y3:** p=8, N=145..150 (n=2,320..2,400).
- **y4:** p=5, N=231..240 (n=2,310..2,400).
- **y5:** p=9 N=129..133 and p=10 N=116..120 (n=2,322..2,400; orders <= 125 are in $S/runs/gtxt).

## (3,10), D = 10, beat 810 (ours)
- **z1:** p=5, N=82..86 (n=820..860); best so far cost 4 at 820: $S/r2/k2/push/r3_N82_g2.sol.best (group 2 of $S/runs/gtxt/g82.txt).
- **z2:** p=6, N=68..70 (cost 4 at 816: $S/r2/k4/runs/C2_N68_g1.sol.best, group 1 of g68) and p=7, N=58 (cost 6 at 812:
  $S/r2/k6/runs/N58_g2_s1.sol.best, group 2 of g58). These states are exact local minima: fresh seeds matter more than restarts.
- **z3:** p=4, N=102..104 (n=816..832) and p=5, N=81 with D=10 but on the 13 groups of order 81 that are not 9 or 12, many seeds
  (n=810 ties; only useful as a source of more 810 graphs for a structure study; at most 4 tasks) — mostly p=4.

## (3,9), D = 9, beat 506 (table; vertex-transitive Haar graph)
- **v1:** p=5 N=51..53 and p=6 N=43..44 (n=510..528); best cost 8 at 510: $S/r2/m1/screen/p5_N51_g1.sol.best (group 1 of g51).
- **v2:** larger bases: p=7 N=37 (518), p=8 N=32 (512; best cost 12: $S/r2/m2/st/p8_g21.sol.best, group 21 of g32),
  p=9 N=29 (522), p=10 N=26 (520), p=11 N=24 (528), p=12 N=22 (528).
