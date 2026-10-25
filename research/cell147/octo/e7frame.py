"""E7 roots (simple-root coordinates, Bourbaki), a frame of 7 mutually orthogonal roots, and the Fano structure of the
remaining roots (each is (sum of +-frame roots over a 4-set)/2)."""
import itertools, sys, numpy as np
sys.path.insert(0, '../ovoid')
from weyl import E7
A = np.array(E7); n = 7
simple = [tuple(int(i == j) for j in range(n)) for i in range(n)]
def dot(u, v): return int(np.array(u) @ A @ np.array(v))
roots = set(simple); fr = list(simple)
while fr:
    nf = []
    for r in fr:
        for i in range(n):
            c = dot(r, simple[i]); s = tuple(r[k] - c * (k == i) for k in range(n))
            if s not in roots: roots.add(s); nf.append(s)
    fr = nf
roots = sorted(roots); print('roots', len(roots))
pos = [r for r in roots if all(x >= 0 for x in r)]
# maximal orthogonal sets of positive roots: search for 7 mutually orthogonal
def ortho_sets():
    res = []
    def rec(cur, start):
        if len(cur) == 7: res.append(list(cur)); return True
        for i in range(start, len(pos)):
            if all(dot(pos[i], c) == 0 for c in cur):
                cur.append(pos[i])
                if rec(cur, i + 1): return True
                cur.pop()
        return False
    rec([], 0); return res
fr7 = ortho_sets()[0]
print('frame:', fr7)
F = np.array(fr7)          # rows: frame roots in root coordinates (norm 2)
# express every root in the frame basis: r = sum c_i f_i with c_i = (r . f_i)/2
coef = {r: tuple(dot(r, f) / 2 for f in fr7) for r in roots}
kinds = {}
for r, c in coef.items():
    supp = tuple(i for i in range(7) if c[i] != 0)
    kinds.setdefault(len(supp), set()).add(supp)
print({k: len(v) for k, v in kinds.items()})
quads = sorted(kinds.get(4, set()))
print('4-sets:', quads)
lines = sorted(tuple(sorted(set(range(7)) - set(qd))) for qd in quads)
print('complements (Fano lines?):', lines)
