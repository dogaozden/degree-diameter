"""Bipartite flag graphs of small classical buildings, built from the definition (independent of weyl_dist.py).

Geometries (field GF(2), GF(3) or GF(4)):
  PG n q        : subspaces of GF(q)^(n+1), dims 1..n                      (type A_n, parameters q)
  Sp n q        : totally isotropic subspaces of GF(q)^(2n), symplectic    (type C_n, q,...,q)
  O n q         : totally singular, parabolic quadric in GF(q)^(2n+1)      (type B_n, q,...,q)   q odd
  Om n q        : totally singular, elliptic quadric in GF(q)^(2n+2)       (type C_n, q,...,q,q^2)
  Op n q        : totally singular, hyperbolic quadric in GF(q)^(2n), dims 1..n-1 (type D_n; a t.s. (n-1)-space
                  stands for the two generators through it)
  U m 2         : totally isotropic for the Hermitian form on GF(4)^m      (m = 2n: C_n (4,..,4,2); m = 2n+1: (4,..,4,8))
Vertices: flags made of the odd-dimensional members of a chamber, and flags made of the even-dimensional members;
adjacent iff together they form a chamber (the two colour classes of the Coxeter diagram, for every type above).
usage: python3 polar_flags.py GEOM n q [edges_out]   -> prints counts, degrees, BFS distance layers from a few
vertices on each side; optionally writes an edge list (first line n, then 'u v') for apsp.c."""
import sys, random
from collections import deque

geom, n, q = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
# ---- field ----
if q in (2, 3):
    add = lambda a, b: (a + b) % q
    mul = lambda a, b: (a * b) % q
    neg = lambda a: (-a) % q
    conj = lambda a: a
elif q == 4:   # GF(4) = {0,1,w,w^2} coded 0,1,2,3 with w^2 = w + 1; addition = xor
    MT = [[0, 0, 0, 0], [0, 1, 2, 3], [0, 2, 3, 1], [0, 3, 1, 2]]
    add = lambda a, b: a ^ b
    mul = lambda a, b: MT[a][b]
    neg = lambda a: a
    conj = lambda a: MT[a][a]          # Frobenius x -> x^2 (the involution of GF(4) over GF(2))
else:
    raise SystemExit("q must be 2, 3 or 4")
F = list(range(q))
# ---- space, forms ----
if geom == 'PG':   dim, top = n + 1, n
elif geom == 'Sp': dim, top = 2 * n, n
elif geom == 'O':  dim, top = 2 * n + 1, n
elif geom == 'Om': dim, top = 2 * n + 2, n
elif geom == 'Op': dim, top = 2 * n, n - 1
elif geom == 'U':  dim, top = n, n // 2
else: raise SystemExit("unknown geometry")
if geom == 'U': assert q == 4
vecs = [()]
for _ in range(dim): vecs = [v + (a,) for v in vecs for a in F]
idx = {v: i for i, v in enumerate(vecs)}
zero = tuple([0] * dim)
def dot_terms(terms):
    s = 0
    for t in terms: s = add(s, t)
    return s
# bilinear / sesquilinear form f(x,y) and quadratic form Q (for orthogonal geometries)
if geom == 'Sp':
    def f(x, y): return dot_terms(add(mul(x[2*i], y[2*i+1]), neg(mul(x[2*i+1], y[2*i]))) for i in range(n))
    Q = None
elif geom == 'U':
    def f(x, y): return dot_terms(mul(x[i], conj(y[dim - 1 - i])) for i in range(dim))   # antidiagonal Hermitian
    Q = None
else:
    if geom == 'O':      # x0^2 + sum x_{2i-1} x_{2i}
        def Q(x): return dot_terms([mul(x[0], x[0])] + [mul(x[2*i+1], x[2*i+2]) for i in range(n)])
    elif geom == 'Op':   # sum x_{2i} x_{2i+1}
        def Q(x): return dot_terms(mul(x[2*i], x[2*i+1]) for i in range(n))
    elif geom == 'Om':   # elliptic: (x0^2 + x0 x1 + e x1^2) + hyperbolic part, x^2+x+e irreducible
        e = 1 if q == 2 else (1 if q == 3 else None)   # q=2: x^2+x+1; q=3: x^2+x+2 irreducible -> e=2
        if q == 3: e = 2
        def Q(x): return dot_terms([mul(x[0], x[0]), mul(x[0], x[1]), mul(e, mul(x[1], x[1]))] +
                                   [mul(x[2*i+2], x[2*i+3]) for i in range(n)])
    if geom != 'PG':
        def f(x, y):    # polar form Q(x+y) - Q(x) - Q(y)
            s = tuple(add(a, b) for a, b in zip(x, y))
            return add(Q(s), neg(add(Q(x), Q(y))))
    else:
        Q = None; f = None
def isotropic_vec(v):
    if geom == 'PG': return True
    if Q is not None: return Q(v) == 0
    return f(v, v) == 0
def perp(u, v):
    if geom == 'PG': return True
    return f(u, v) == 0
nz = [v for v in vecs if v != zero and isotropic_vec(v)]
def span_add(S, members, v):
    """S: bitmask of a subspace, members: its vectors; return bitmask and members of S + <v>."""
    newm = set(members)
    for a in F:
        if a == 0: continue
        av = tuple(mul(a, c) for c in v)
        for m in members:
            newm.add(tuple(add(x, y) for x, y in zip(m, av)))
    mask = 0
    for m in newm: mask |= 1 << idx[m]
    return mask, tuple(sorted(newm))
# ---- enumerate chambers: chains V1 < ... < V_top of totally isotropic/singular subspaces ----
mem = {0: (zero,)}    # bitmask -> members
start = 1 << idx[zero]
mem = {start: (zero,)}
ext_cache = {}
def extensions(S):
    if S in ext_cache: return ext_cache[S]
    members = mem[S]
    out = set()
    for v in nz:
        if S >> idx[v] & 1: continue
        if all(perp(m, v) for m in members):
            mask, mm = span_add(S, members, v)
            if mask not in mem: mem[mask] = mm
            out.add(mask)
    ext_cache[S] = sorted(out)
    return ext_cache[S]
chambers = []
def rec(chain):
    if len(chain) == top: chambers.append(tuple(chain)); return
    for T in extensions(chain[-1] if chain else start): rec(chain + [T])
sys.setrecursionlimit(10000)
rec([])
odd, even, edges = {}, {}, []
for c in chambers:
    o = tuple(c[i] for i in range(0, top, 2)); e_ = tuple(c[i] for i in range(1, top, 2))
    oi = odd.setdefault(o, len(odd)); ei = even.setdefault(e_, len(even)); edges.append((oi, ei))
No, Ne = len(odd), len(even); nv = No + Ne
adj = [[] for _ in range(nv)]
for a, b in edges: adj[a].append(No + b); adj[No + b].append(a)
dodd = sorted({len(adj[i]) for i in range(No)}); deven = sorted({len(adj[No + i]) for i in range(Ne)})
print(f"{geom} n={n} q={q}: chambers {len(chambers)}, vertices {nv} (odd-dim flags {No}, even-dim flags {Ne}), "
      f"degrees odd {dodd} even {deven}")
def bfs(s):
    dist = [-1] * nv; dist[s] = 0; dq = deque([s]); layer = {}
    while dq:
        u = dq.popleft()
        for w in adj[u]:
            if dist[w] < 0: dist[w] = dist[u] + 1; dq.append(w)
    for d in dist: layer[d] = layer.get(d, 0) + 1
    return dict(sorted(layer.items()))
random.seed(1)
for side, lo, hi in (("odd", 0, No), ("even", No, nv)):
    srcs = [lo] + random.sample(range(lo, hi), min(3, hi - lo - 1))
    layers = [bfs(s) for s in srcs]
    same = all(L == layers[0] for L in layers)
    print(f"  from {side}-dim flags ({len(srcs)} sources, identical layers: {same}): {layers[0]}")
if len(sys.argv) > 4:
    with open(sys.argv[4], 'w') as fo:
        fo.write(f"{nv}\n"); fo.writelines(f"{a} {No + b}\n" for a, b in edges)
