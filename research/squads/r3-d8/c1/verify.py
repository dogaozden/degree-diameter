#!/usr/bin/env python3
"""Independent numpy check of near-duality outputs (card c1): recomputes relations from the gh file."""
import sys
from pathlib import Path
import numpy as np

SHARED = Path('/home/user/degree-diameter/research/squads/r3-d8/shared')

def main():
    q = int(sys.argv[1])
    with open(SHARED / f'gh{q}.txt') as fh:
        qq, N = map(int, fh.readline().split())
        lines = [[int(x) for x in fh.readline().split()] for _ in range(N)]
    A = np.zeros((N, N), dtype=np.float32)          # A[p, k] = 1 if point p on line k
    for k in range(N):
        A[lines[k], k] = 1
    assert (A.sum(axis=0) == q + 1).all() and (A.sum(axis=1) == q + 1).all()
    Lc = (A.T @ A > 0).astype(np.float32); np.fill_diagonal(Lc, 0)      # concurrent lines
    I = np.eye(N, dtype=np.float32)
    R1 = I + Lc
    R2 = ((R1 @ R1) > 0).astype(np.float32)
    R3 = ((R2 @ R1) > 0)
    assert R3.all(), 'line graph diameter > 3'                           # incidence diameter <= 6
    L2 = ((Lc @ Lc) > 0) & (Lc == 0) & (I == 0)                          # distance 4 in incidence graph
    Opp = (~(R1.astype(bool) | L2))                                      # distance 6
    Pc = (A @ A.T > 0); np.fill_diagonal(Pc, False)                       # collinear points
    for name, s_file in [('h1', sys.argv[2]), ('h2', sys.argv[3]) if len(sys.argv) > 3 else None]:
        pass
    outs = {}
    for arg in sys.argv[2:]:
        s = np.array([int(x) for x in open(arg).read().split()])
        assert sorted(s.tolist()) == list(range(N)), 'not a bijection'
        flag = A[np.arange(N), s].sum()
        us, xs = np.nonzero(np.triu(Pc, 1))
        conc = Lc[s[us], s[xs]].sum(); opp = Opp[s[us], s[xs]].sum(); E = len(us)
        outs[arg] = (int(conc), int(opp), int(E), int(flag))
        print(f'{arg}: E {E} conc {conc} ({conc/E:.5f}) opp {opp} ({opp/E:.5f}) flags_on_hop {int(flag)}')
    if len(sys.argv) > 3:
        s1 = np.array([int(x) for x in open(sys.argv[2]).read().split()])
        s2 = np.array([int(x) for x in open(sys.argv[3]).read().split()])
        print('hop1 == hop2 at points:', int((s1 == s2).sum()))

if __name__ == '__main__':
    main()
