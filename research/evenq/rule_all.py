"""For every (c0, c1): is the formula whisker set exact, and does G have no zero?  Expect: exact <=> G zero-free.
python3 rule_all.py q [delta]"""
import sys
import numpy as np
from frame import Frame
q = int(sys.argv[1]); Fr = Frame(q, int(sys.argv[2]) if len(sys.argv) > 2 else None)
H, N, lines, F = Fr.H, Fr.N, Fr.H.lines, Fr.H.F
ADD, MUL, INV = F.ADD, F.MUL, F.INV; d = Fr.delta; P = H.P
num = ADD[ADD[MUL[P[:, 2], P[:, 3]], MUL[P[:, 2], P[:, 4]]], MUL[P[:, 4], P[:, 5]]]
den = ADD[ADD[MUL[d, MUL[P[:, 2], P[:, 2]]], MUL[P[:, 2], P[:, 5]]], MUL[P[:, 5], P[:, 5]]]
nu = MUL[num, INV[den]]
def G(c0, c1, a, b):
    nrm = ADD[ADD[MUL[a, a], MUL[a, b]], MUL[d, MUL[b, b]]]
    return ADD[MUL[ADD[MUL[c0, a], MUL[c1, b]], nrm], MUL[b, MUL[b, b]]]
Sz = {}
for a in range(q):
    for b in range(q):
        if (a, b) != (0, 0):
            ms = [int(m) for m in Fr.Sz(a, b) if m != Fr.v]
            Sz[(a, b)] = (ms, np.array([nu[[y for y in lines[m] if Fr.inPi[y]][0]] for m in ms]))
agree = 0
for c0 in range(q):
    for c1 in range(q):
        W = []
        for (a, b), (ms, nus) in Sz.items():
            nrm = int(ADD[ADD[MUL[a, a], MUL[a, b]], MUL[d, MUL[b, b]]])
            Fz = int(MUL[G(c0, c1, a, b), INV[nrm]])
            W += [m for m, x in zip(ms, nus) if x == Fz]
        cov = np.zeros(N, int)
        for m in W: cov[lines[m]] += 1
        exact = bool(np.all(cov[Fr.free] == 1))
        zf = all(G(c0, c1, a, b) != 0 for a in range(q) for b in range(q) if (a, b) != (0, 0))
        agree += exact == zf
print(f'q={q} delta={d}: exact <=> G zero-free holds for {agree} of {q*q} pairs (c0,c1)')
