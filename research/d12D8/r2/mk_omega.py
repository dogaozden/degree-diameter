"""Gomez (1986 thesis, sec. 2.9.3) bipartite compound Omega B_1, as read from Figs 2.21a/b: 5*alpha copies of B_1 = H(q)
incidence graph (groups of 5, type a or b), plus 5 hubs per vertex t of B_1 (hub (t,k), k in Z_5), adjacent to the
copies of t in 2 copies of each group. Type a: point-hub k ~ copies k-1, k+1; line-hub k ~ copies k+2, k+3.
Type b: point-hub k ~ copies k+3, k+4; line-hub k ~ copies k-1, k+1.
usage: mk_omega.py q TYPES out      (TYPES e.g. "aab": one letter per group)   writes "N" + edge list"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
from hexlib import load_hex
q, types, out = int(sys.argv[1]), sys.argv[2], sys.argv[3]
n, lines = load_hex(q); N1 = 2 * n; C = 5 * len(types)
nv = C * N1 + 5 * N1
def cid(c, t): return c * N1 + t
def hid(t, k): return C * N1 + t * 5 + k
E = []
for c in range(C):
    for l in range(n):
        for p in lines[l]: E.append((cid(c, int(p)), cid(c, n + l)))
for g, ty in enumerate(types):
    base = 5 * g
    for t in range(N1):
        isp = t < n
        for k in range(5):
            if ty == 'a': cs = [k - 1, k + 1] if isp else [k + 2, k + 3]
            else: cs = [k + 3, k + 4] if isp else [k - 1, k + 1]
            for c in cs: E.append((hid(t, k), cid(base + c % 5, t)))
with open(out, 'w') as f:
    f.write(f"{nv}\n")
    for a, b in E: f.write(f"{a} {b}\n")
print(nv, len(E))
