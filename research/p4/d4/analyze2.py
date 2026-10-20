"""Describe M in the spread-line coordinates: line z in K or inf, point index i in Z_{q+1} (point = gamma^i * v_z)."""
import json, sys
from w3k import W3
d = json.load(open(sys.argv[1]))
W = W3(d['q']); q = W.q; Q = q*q
M = set(d['M'])
def coords(p):
    a, b = W.pts[p]
    if a == 0:
        return 'inf', int(W.log[b]) % (q+1)
    z = int(W.mul[b, W.K.inv(a)])
    return z, int(W.log[a]) % (q+1)
by = {}
for p in M:
    z, i = coords(p)
    by.setdefault(z, []).append(i)
diffs = {}
for z, I in by.items():
    if len(I) == 2:
        dd = (I[1]-I[0]) % (q+1); dd = min(dd, q+1-dd)
        diffs[dd] = diffs.get(dd, 0) + 1
print('pair index differences:', diffs)
print('lines used:', len(by), 'sizes', sorted(len(v) for v in by.values()))
for z in sorted(by, key=lambda t: (t == 'inf', t if t != 'inf' else 0)):
    zl = 'inf' if z == 'inf' else ('0' if z == 0 else f'g^{int(W.log[z])}')
    print(zl, sorted(by[z]), end='; ')
print()
