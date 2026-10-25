"""Write the edge list (n, then "u v") of the polygon cover with units, hub links and super-hubs.
Usage: python3 unit_edges2.py GHFILE STATE UNITFILE EXTRAS|- OUT.edges
Lift vertex (x, c) -> x*m + c (points 0..P-1, lines P..2P-1); unit i adds z_i = 2Pm + 2i (joined to (p_i, c) for all c)
and z'_i = 2Pm + 2i + 1 (joined to (l_i, c), l_i = sigma_{t_i}(p_i)); the matching edges (p_i, l_i) are deleted in
every copy. EXTRAS (as for uhcheck): "NS" then lines "a b" joining new vertices a, b (hubs 0..2NU-1, then super-hubs
2NU..2NU+NS-1), written as 2Pm + a, 2Pm + b. Units files may have a third column (the line), which is checked."""
import sys
sys.path.insert(0, '..')
from ghtools import load_gh, read_state
ghf, stf, uf, xf, out = sys.argv[1:6]
P, q, lines, adj = load_gh(ghf)
J, m, sig, hv, fv = read_state(stf, P, q)
units = []
for l in open(uf):
    a = l.split()
    if len(a) < 2: continue
    p, t = int(a[0]), int(a[1])
    if len(a) > 2: assert int(a[2]) == sig[p][t - 1], 'unit line mismatch'
    units.append((p, t))
uset = set((p, t - 1) for p, t in units)
assert len(uset) == len(units)
NS = 0; X = []
if xf != '-':
    with open(xf) as f:
        NS = int(f.readline())
        for l in f:
            a = l.split()
            if len(a) == 2: X.append((int(a[0]), int(a[1])))
base = 2 * P * m
n = base + 2 * len(units) + NS
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
        E.append((base + 2 * i, p * m + c))
        E.append((base + 2 * i + 1, (P + l) * m + c))
for a, b in X: E.append((base + a, base + b))
with open(out, 'w') as f:
    f.write('%d\n' % n)
    f.write(''.join('%d %d\n' % e for e in E))
print('n=%d edges=%d units=%d superhubs=%d extra_edges=%d' % (n, len(E), len(units), NS, len(X)))
