"""Write the edge list (n, then "u v") of the polygon cover with units.
Usage: python3 unit_edges.py GHFILE STATE UNITFILE OUT.edges
Lift vertex (x, c) -> x*m + c (x: points 0..P-1, lines P..2P-1); unit i adds z_i = 2Pm + 2i (joined to (p_i, c) for all c)
and z'_i = 2Pm + 2i + 1 (joined to (l_i, c), l_i = sigma_{t_i}(p_i)); the matching edges (p_i, l_i) are deleted in every copy."""
import sys
sys.path.insert(0, '..')
from ghtools import load_gh, read_state
ghf, stf, uf, out = sys.argv[1:5]
P, q, lines, adj = load_gh(ghf)
J, m, sig, hv, fv = read_state(stf, P, q)
units = [tuple(map(int, l.split())) for l in open(uf) if l.strip()]
uset = set((p, t - 1) for p, t in units)
n = 2 * P * m + 2 * len(units)
E = []
for L, pts in enumerate(lines):
    for k, x in enumerate(pts):
        h = fv[L][k]
        for c in range(m): E.append((x * m + c, (P + L) * m + (c + h) % m))
for x in range(P):
    for t in range(J):
        if (x, t) in uset: continue
        L, h = sig[x][t], hv[x][t]
        for c in range(m): E.append((x * m + c, (P + L) * m + (c + h) % m))
for i, (p, t) in enumerate(units):
    l = sig[p][t - 1]
    for c in range(m):
        E.append((2 * P * m + 2 * i, p * m + c))
        E.append((2 * P * m + 2 * i + 1, (P + l) * m + c))
with open(out, 'w') as f:
    f.write('%d\n' % n)
    for a, b in E: f.write('%d %d\n' % (a, b))
print('n=%d edges=%d units=%d' % (n, len(E), len(units)))
