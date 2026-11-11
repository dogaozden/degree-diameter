#!/usr/bin/env python3
"""Independent rebuild of the graph `omega` of lean/BipartiteDD/LeanMaxx/Omega3/Graph.lean over GF(p), p prime.

H(q) is built from the definition in Hexagon/Defs.lean (quadric x0x4+x1x5+x2x6-x3^2, lines = totally singular
lines whose Grassmann coordinates satisfy Tits' six equations), NOT from any code of the note.  Omega is built
from `metPos`/`omegaRel` (Wiring.lean / Graph.lean), labelling mu c = 1 (thesis), eps0 = 0 (reading 2).
Usage: build_omega.py p pattern out.edges    (pattern: string over {a,b}, a = type false, b = type true)
"""
import sys, itertools

p = int(sys.argv[1]); pattern = sys.argv[2]; out = sys.argv[3]
eps0 = int(sys.argv[4]) if len(sys.argv) > 4 else 0
q = p
alpha = len(pattern)
typ = [c == 'b' for c in pattern]

def Q(x): return (x[0]*x[4] + x[1]*x[5] + x[2]*x[6] - x[3]**2) % p
def Bf(x, y):
    return (x[0]*y[4] + x[4]*y[0] + x[1]*y[5] + x[5]*y[1] + x[2]*y[6] + x[6]*y[2] - 2*x[3]*y[3]) % p
def pl(x, y, i, j): return (x[i]*y[j] - x[j]*y[i]) % p
def tits(x, y):
    return (pl(x,y,1,2) == pl(x,y,3,4) and pl(x,y,5,4) == pl(x,y,3,2) and pl(x,y,2,0) == pl(x,y,3,5)
            and pl(x,y,6,5) == pl(x,y,3,0) and pl(x,y,0,1) == pl(x,y,3,6) and pl(x,y,4,6) == pl(x,y,3,1))
def norm(x):
    for c in x:
        if c % p:
            inv = pow(c, -1, p)
            return tuple((inv*t) % p for t in x)
    return None

pts = []
for x in itertools.product(range(p), repeat=7):
    if any(x) and norm(x) == x and Q(x) == 0:
        pts.append(x)
N = len(pts)
assert N == (q**6 - 1)//(q - 1), N
pidx = {x: i for i, x in enumerate(pts)}

lines = {}
for i, x in enumerate(pts):
    for y in pts[i+1:]:
        if Bf(x, y) == 0 and tits(x, y):
            S = set()
            for a in range(p):
                for b in range(p):
                    if a or b:
                        v = norm(tuple((a*xi + b*yi) % p for xi, yi in zip(x, y)))
                        S.add(v)
            lines[frozenset(S)] = None
L = list(lines)
assert len(L) == N, len(L)
assert all(len(l) == q + 1 for l in L)
# incidence graph beta: vertices 0..N-1 points (klass 0), N..2N-1 lines (klass 1)
nB = 2*N
adjB = [[] for _ in range(nB)]
for j, l in enumerate(L):
    for x in l:
        i = pidx[x]
        adjB[i].append(N + j); adjB[N + j].append(i)
assert all(len(a) == q + 1 for a in adjB)
kappa = [0]*N + [1]*N

def bfs(adj, s):
    d = [-1]*len(adj); d[s] = 0; fr = [s]
    while fr:
        nf = []
        for u in fr:
            for v in adj[u]:
                if d[v] < 0: d[v] = d[u] + 1; nf.append(v)
        fr = nf
    return d
d0 = bfs(adjB, 0); d1 = bfs(adjB, N)
assert max(d0) == 6 and max(d1) == 6, (max(d0), max(d1))
# girth 12: no cycle shorter than 12 -> every ball of radius 5 is a tree (sphere sizes 1,q+1,(q+1)q,...)
sizes = [sum(1 for t in d0 if t == r) for r in range(7)]
assert sizes == [1, q+1] + [(q+1)*q**(r-1) for r in range(2, 6)] + [q**5], sizes
print(f"H({q}): N={N}, incidence graph diameter 6, sphere sizes from a point {sizes}", file=sys.stderr)

def metPos(ty, bar, k, i):
    if (not ty) and (not bar): return i in ((k-1) % 5, (k+1) % 5)
    if (not ty) and bar:       return i in ((k+2) % 5, (k+3) % 5)
    if ty and (not bar):       return i in ((k+3) % 5, (k+4) % 5)
    return i in ((k-1) % 5, (k+1) % 5)

# vertices: copy vertex (b, i, y) -> ((b*5+i)*nB + y); hubs after
ncopy = 5*alpha
def cv(b, i, y): return (b*5 + i)*nB + y
base = ncopy*nB
hubs = []   # (bar, k, r)
for bar in (0, 1):
    colr = (eps0 + bar) % 2   # hubcol
    for k in range(5):
        for r in range(nB):
            if kappa[r] == colr: hubs.append((bar, k, r))
hid = {h: base + n for n, h in enumerate(hubs)}
V = base + len(hubs)
edges = []
for c in range(ncopy):
    for u in range(nB):
        for v in adjB[u]:
            if u < v: edges.append((c*nB + u, c*nB + v))
for (bar, k, r), h in hid.items():
    for b in range(alpha):
        for i in range(5):
            if metPos(typ[b], bool(bar), k, i):
                edges.append((h, cv(b, i, r)))   # mu c = 1
with open(out, 'w') as f:
    f.write(f"{V} {len(edges)} {base}\n")
    for u, v in edges: f.write(f"{u} {v}\n")
print(f"omega: p={p} pattern={pattern} eps0={eps0}: V={V}, E={len(edges)}, hubs={len(hubs)} (10N={10*N})", file=sys.stderr)
