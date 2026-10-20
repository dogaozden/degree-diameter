"""The explicit exact whisker set for even q (char-2 analogue of hats Theorem 4), built and checked directly.

Pi_z : X3 = X0 + d X4 + a X2 + b X5  (Tr(d) = 1),  S_z = H(q)-lines inside Pi_z,  v = <e1, e6>.
nu(X) = (X2X3 + X2X4 + X4X5) / (d X2^2 + X2X5 + X5^2)            (X in Pi, not on v)
G(a,b) = (c0 a + c1 b)(a^2 + ab + d b^2) + b^3,  F(z) = G(z)/(a^2 + ab + d b^2)
W = { m in S_z \\ {v} : z != 0, nu(m cap Pi) = F(z) }.

python3 rule.py q [delta] [c0 c1]   -> whiskers_formula_q{q}.json, prints the exactness check
"""
import json
import sys
import time

import numpy as np

from frame import Frame

t0 = time.time()
q = int(sys.argv[1])
delta = int(sys.argv[2]) if len(sys.argv) > 2 else None
Fr = Frame(q, delta)
H, N, lines, F = Fr.H, Fr.N, Fr.H.lines, Fr.H.F
ADD, MUL, INV = F.ADD, F.MUL, F.INV
d = Fr.delta


def G(c0, c1, a, b):
    nrm = ADD[ADD[MUL[a, a], MUL[a, b]], MUL[d, MUL[b, b]]]
    return ADD[MUL[ADD[MUL[c0, a], MUL[c1, b]], nrm], MUL[b, MUL[b, b]]]


A_, B_ = np.meshgrid(np.arange(q), np.arange(q), indexing='ij')
nz = (A_ != 0) | (B_ != 0)
good = [(c0, c1) for c0 in range(q) for c1 in range(q) if np.all(G(c0, c1, A_, B_)[nz] != 0)]
print(f'q={q} delta={d}: {len(good)} good (c0,c1) of {q*q}', flush=True)
if len(sys.argv) > 4:
    c0, c1 = int(sys.argv[3]), int(sys.argv[4])
    assert (c0, c1) in good
else:
    if not good:
        raise SystemExit('no good (c0,c1)')
    c0, c1 = good[0]
P = H.P
num = ADD[ADD[MUL[P[:, 2], P[:, 3]], MUL[P[:, 2], P[:, 4]]], MUL[P[:, 4], P[:, 5]]]
den = ADD[ADD[MUL[d, MUL[P[:, 2], P[:, 2]]], MUL[P[:, 2], P[:, 5]]], MUL[P[:, 5], P[:, 5]]]
onv = np.zeros(N, bool)
onv[lines[Fr.v]] = True
assert np.all(den[Fr.inPi & ~onv] != 0)
nu = MUL[num, INV[den]]
# nu constant on S-lines (remark in the paper)
Sn = [s for s in Fr.S if s != Fr.v]
const = all(len(set(nu[lines[s]].tolist())) == 1 for s in Sn)
W = []
for a in range(q):
    for b in range(q):
        if (a, b) == (0, 0):
            continue
        nrm = int(ADD[ADD[MUL[a, a], MUL[a, b]], MUL[d, MUL[b, b]]])
        Fz = int(MUL[G(c0, c1, a, b), INV[nrm]])
        for m in Fr.Sz(a, b):
            if m == Fr.v:
                continue
            X = [y for y in lines[m] if Fr.inPi[y]]
            assert len(X) == 1
            if nu[X[0]] == Fz:
                W.append(int(m))
cov = np.zeros(N, int)
for m in W:
    cov[lines[m]] += 1
exact = bool(np.all(cov[Fr.free] == 1))
opp = bool(np.all(Fr.dist[N + np.array(W)] == 6)) and not (set(W) & set(Fr.S.tolist()))
print(f'c0={c0} c1={c1}: nu constant on S-lines {const}; |W| = {len(W)} (q^2(q^2-1) = {q*q*(q*q-1)}); '
      f'opposite v, not in S: {opp}; every free point on exactly one whisker: {exact}  [{time.time()-t0:.0f}s]')
json.dump({'q': q, 'delta': int(d), 'c0': int(c0), 'c1': int(c1), 'v': Fr.v, 'S': Fr.S.tolist(), 'whiskers': sorted(W)},
          open(f'whiskers_formula_q{q}.json', 'w'))
