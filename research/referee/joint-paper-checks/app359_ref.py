"""Referee check of Appendix A (the (7,4) example): parse the printed rows, check the claims of 'What to check by
hand', build the 359-vertex graph for the C checker."""
import itertools, re
q = 5
def norm(v):
    for c in v:
        if c % q:
            ic = pow(c, q - 2, q); return tuple((ic * x) % q for x in v)
Qf = lambda v: (v[0]*v[0] + v[1]*v[2] + v[3]*v[4]) % q
pts = sorted(set(norm(v) for v in itertools.product(range(q), repeat=5) if any(v) and Qf(v) == 0))
assert len(pts) == 156
# lines of Q(4,5): pairs of perpendicular points spanning a totally singular line
def b(u, v): return (2*u[0]*v[0] + u[1]*v[2] + u[2]*v[1] + u[3]*v[4] + u[4]*v[3]) % q
lines = set()
for u, v in itertools.combinations(pts, 2):
    if b(u, v) == 0:
        lines.add(frozenset(norm(tuple((s*x + v_) % q for x, v_ in zip(u, v))) for s in range(q)) | {u})
lines = sorted(lines, key=sorted); assert len(lines) == 156 and all(len(L) == 6 for L in lines)
O = [p for p in pts if (p[4] - 2*p[3]) % q == 0]; assert len(O) == 26
assert all(len(set(L) & set(O)) == 1 for L in lines)
rows = []
for line in open('app359_rows.txt'):
    toks = re.findall(r'\(([0-9:]+)\)(\*?)', line)
    if not toks: continue
    rows.append([(tuple(int(x) for x in t.split(':')), s == '*') for t, s in toks])
assert len(rows) == 21 and all(len(r) == 6 for r in rows)
for r in rows:
    S = frozenset(p for p, _ in r); assert S in set(lines), r
# pairwise intersections
inter = {}
for i, j in itertools.combinations(range(21), 2):
    I = set(p for p, _ in rows[i]) & set(p for p, _ in rows[j])
    if I: inter[(i + 1, j + 1)] = I
print("pairs of rows that meet:", {k: sorted(v) for k, v in inter.items()})
stars = [(i + 1, p) for i, r in enumerate(rows) for p, s in r if s]
print("starred:", stars, " all starred on ovoid:", all(p in O for _, p in stars))
# build graph
pid = {p: i for i, p in enumerate(pts)}; lid = {L: 156 + i for i, L in enumerate(lines)}
edges = [(pid[p], lid[L]) for L in lines for p in L]
cl = {o: 312 + i for i, o in enumerate(O)}
for o in O:
    for L in lines:
        if o in L: edges.append((cl[o], lid[L]))
for k, r in enumerate(rows):
    y = 338 + k
    for p, s in r: edges.append(((cl[p] if s else pid[p]), y))
N = 359
open('app359.edges', 'w').write(f"{N} {len(edges)}\n" + "\n".join(f"{u} {v}" for u, v in edges) + "\n")
print("written app359.edges with", N, "vertices")
