"""Slope of Phi_p(z) = nu(X_p(z)) + h(z) along A_p (step (p5, p2), L0(p) = 1); check affine and fit the slope.
python3 slope.py q [delta]"""
import itertools, sys
import numpy as np
import affine as A
import frame
q = int(sys.argv[1])
if len(sys.argv) > 2:
    _o = frame.Frame.__init__
    frame.Frame.__init__ = lambda self, q, delta=None, log=print: _o(self, q, int(sys.argv[2]), log)
A.setup(q, 'lines')
F, Fr, P = A.F, A.Fr, A.P
ADD, MUL, INV = F.ADD, F.MUL, F.INV
d = Fr.delta; d2 = int(MUL[d, d])
def nu_pt(X):
    num = ADD[ADD[MUL[X[2], X[3]], MUL[X[2], X[4]]], MUL[X[4], X[5]]]
    den = ADD[ADD[MUL[d, MUL[X[2], X[2]]], MUL[X[2], X[5]]], MUL[X[5], X[5]]]
    return int(MUL[num, INV[den]])
def hz(a, b):
    num = MUL[b, MUL[b, b]]
    den = ADD[ADD[MUL[a, a], MUL[a, b]], MUL[d, MUL[b, b]]]
    return int(MUL[num, INV[den]])
nu = {s: nu_pt(P[A.lines[s][0]]) for s in A.kidx}
inv_k = {i: s for s, i in A.kidx.items()}
aff_ok, sl = True, {}
for p in Fr.free:
    pr, (p2, p5) = A.params[int(p)]
    f = [nu[inv_k[k]] ^ hz(*A.zs[z]) for k, z in pr]
    slope_ = f[1] ^ f[0]
    for t in range(q):
        aff_ok &= f[t] == (f[0] ^ int(MUL[t, slope_]))
    key = (p2, p5)
    sl.setdefault(key, set()).add(slope_)
print('q', q, 'delta', d, 'Phi affine on every A_p:', aff_ok, '; slope a function of (p2,p5):', all(len(v) == 1 for v in sl.values()), len(sl))
# fit slope * N(p2,p5) = cubic in (p2,p5), N = p2^2 + d2 p2 p5 + d2 p5^2
keys = list(sl); vals = np.array([next(iter(sl[k])) for k in keys])
p2 = np.array([k[0] for k in keys]); p5 = np.array([k[1] for k in keys])
Nn = ADD[ADD[MUL[d, MUL[p2, p2]], MUL[p2, p5]], MUL[p5, p5]]
lhs = MUL[vals, Nn]
for co in itertools.product(range(q), repeat=4):
    c = [MUL[MUL[MUL[p2, p2], p2], co[0]], MUL[MUL[MUL[p2, p2], p5], co[1]], MUL[MUL[MUL[p2, p5], p5], co[2]], MUL[MUL[MUL[p5, p5], p5], co[3]]]
    if np.all(ADD[ADD[c[0], c[1]], ADD[c[2], c[3]]] == lhs):
        print('slope = (p2^3, p2^2p5, p2p5^2, p5^3) .', co, '/ (d p2^2 + p2p5 + p5^2)')
