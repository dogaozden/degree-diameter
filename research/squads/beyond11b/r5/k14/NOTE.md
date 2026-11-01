# k14 hole anatomy (round 5)

Tool: holes.c (BFS of H(G,S) from (e,A) and (e,B), meta groups, n=1). Its cost matches haar_gen3s (start cost 3 on c0 file).

| state | cell | cost | holes (side, (a,j), inverse, inverse is hole, dist) |
|---|---|---|---|
| s0_f677.txt (k01) | (4,12) Z677 x| Z52 | 3: B-side, (301,26) self-inverse; (332,42)<->(205,10) not a pair; (507,9)<->(494,43) not a pair (dist 13) |
| c11.best.txt | (4,12) same | 1 | 1: B-side (540,26), self-inverse involution, dist 13 |
| c05.best.txt | (5,11) Z5023 x| Z31 | 4: A (3081,26)<->(3435,5) inverse pair; B (1003,2)<->(3769,29) inverse pair; dist 12 |

Runs (runs.txt): (4,12) cost 3 plateau over 4 runs (K=4,8; chains); fresh K=8 run reached 1 (c11). (5,11) cost 4 after
4 runs (c04,c05,c10 at K=2,4,8); cost 6 (c08,c09). No cost-2 state obtained.

Conclusion (measured, small sample): at odd D the A-ball and B-ball are inverse-closed (T = S^-1 S and S S^-1 are symmetric),
so every side's holes come in inverse pairs or as self-inverse elements; the cost-4 (5,11) state is two pairs (one per side).
A cost-2 odd-D state would then be one inverse pair on one side, which matches the lemma but was not observed here.
At even D the holes are not inverse-closed (the B-ball from (e,A) is not symmetric): the (4,12) states have
isolated holes, including an involution (540,26) at cost 1. A finishing move for (5,11) must add/swap a generator
so that the pair (x, x^-1) on one side is covered: it must change the words of length <= 5 in S^-1 S that hit x, which
means moving a generator whose change does not uncover a third element; plain annealing at cost 4 did not do that in 4 runs.
