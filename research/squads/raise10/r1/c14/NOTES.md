c14 (7,10) haar_big0 FIXF, ORBIT "3 2 1" (f=1, m=2 alpha-orbits of size 3, d=7), BOUNDCUR where stated.
Runs (90 s each, THREADS=1), best cost reached above the target (need cost 0 at N >= 1,149,121):
- psl 19 x Z337 (N=1152540): a1 cost 21 (FIXF, seed 1), c1 cost 24 (no FIXF, seed 4), f1 cost 27 (FIXF, default T, seed 8),
  a2/a3/h1 chains from a1.sol.best stayed at 21 (T 0.15 and reheat T 0.6 and T 0.3).
- psl 13 x Z1057 (N=1154244): b1 cost 315 (default T).   psl 13 x Z1063 (N=1160796): e1 cost 288.
- psl 23 x Z193 (N=1171896): d1 cost 30.   sl 19 x Z169 (N=1155960): g1 cost 27.
EVAL check (eval.log): a1.sol.best recomputed by full count = 21, FIXF screen agrees (0 fixed holes, 21 holes elsewhere).
Reading: the 2-orbit slot space plateaus at 21-30 on every group tried; no cost-0 or cost-1 state found.
- later: i1 psl 19 x Z343 (N 1173060) cost 39 (FIXF, seed 11); j1 chain from a1.sol.best with K=16, T 0.4 stayed at 21.
