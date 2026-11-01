#!/usr/bin/env python3
"""gq.py: incidence graph of W(3) = GQ(3,3) (40 points, 40 totally isotropic lines, 80 vertices, 4-regular, girth 8).
Writes base.txt (lift format: 80, then 'u v' with points 0..39 and lines 40..79) and perms (one per order requested).
Automorphisms: random products of symplectic transvections (elements of Sp(4,3)) acting on points and lines."""
import random, sys, itertools, collections
P = 3
def B(x, y):  # symplectic form
    return (x[0]*y[1] - x[1]*y[0] + x[2]*y[3] - x[3]*y[2]) % P
def norm(v):
    for c in v:
        if c % P:
            inv = 1 if c % P == 1 else 2
            return tuple((inv*t) % P for t in v)
    return None
vecs = [v for v in itertools.product(range(P), repeat=4) if any(v)]
pts = sorted({norm(v) for v in vecs})
assert len(pts) == 40
idx = {p: i for i, p in enumerate(pts)}
lines = set()
for p, q in itertools.combinations(pts, 2):
    if B(p, q) == 0:
        span = set()
        for a, b in itertools.product(range(P), repeat=2):
            if a or b:
                span.add(norm(tuple((a*x + b*y) % P for x, y in zip(p, q))))
        lines.add(frozenset(idx[s] for s in span))
lines = sorted(lines, key=lambda s: sorted(s))
assert len(lines) == 40 and all(len(L) == 4 for L in lines)
edges = []
for j, L in enumerate(lines):
    for i in L:
        edges.append((i, 40 + j))
def apply_mat(M, v):
    return tuple(sum(M[r][c]*v[c] for c in range(4)) % P for r in range(4))
def transvection(v, a):
    # x -> x + a B(x,v) v  as a matrix: columns = images of basis vectors
    cols = []
    for k in range(4):
        e = [0]*4; e[k] = 1
        bx = B(e, v)
        cols.append([(e[r] + a*bx*v[r]) % P for r in range(4)])
    return [[cols[c][r] for c in range(4)] for r in range(4)]
def matmul(A, Bm):
    return [[sum(A[r][k]*Bm[k][c] for k in range(4)) % P for c in range(4)] for r in range(4)]
def perm_of(M):
    pm = []
    for p in pts:
        pm.append(idx[norm(apply_mat(M, p))])
    return pm
def order_of(pm):
    cur = list(range(40)); k = 0
    while True:
        cur = [pm[x] for x in cur]; k += 1
        if cur == list(range(40)): return k
def check_auto(pm):
    es = {frozenset(e) for e in edges}
    return all(frozenset((pm[u], pm[v] if v < 40 else v)) in es or True for u, v in edges) and all(
        frozenset((pm[u], lines_map[v])) in es for u, v in edges) if False else True
def line_perm(pm):
    lm = []
    for L in lines:
        img = frozenset(pm[i] for i in L)
        lm.append(lines.index(img) if img in lines else None)
    return lm
if __name__ == '__main__':
    random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    want = [int(x) for x in sys.argv[2].split(',')] if len(sys.argv) > 2 else [5]
    with open('base_gq33.txt', 'w') as f:
        f.write('80\n' + ''.join(f'{u} {v}\n' for u, v in sorted(edges)))
    eset = {frozenset(e) for e in edges}
    found = {}
    tries = 0
    while any(w not in found for w in want) and tries < 200000:
        tries += 1
        M = [[int(r == c) for c in range(4)] for r in range(4)]
        for _ in range(30):
            v = tuple(random.randrange(P) for _ in range(4))
            if not any(v): continue
            M = matmul(transvection(v, random.randrange(1, P)), M)
        pm = perm_of(M)
        if len(set(pm)) != 40: continue
        k = order_of(pm)
        if k in want and k not in found:
            lm = line_perm(pm)
            if None in lm: continue
            full = pm + [40 + x for x in lm]
            ok = all(frozenset((full[u], full[v])) in eset for u, v in edges)
            assert ok
            found[k] = full
    for k, full in found.items():
        with open(f'base_gq33_o{k}.perm', 'w') as f:
            f.write(' '.join(map(str, full)) + '\n')
        orbs = []; seen = set()
        for x in range(80):
            if x in seen: continue
            o = []; y = x
            while y not in seen:
                seen.add(y); o.append(y); y = full[y]
            orbs.append(len(o))
        print(f'order {k}: vertex orbits {len(orbs)} sizes {collections.Counter(orbs)} (tries {tries})')
