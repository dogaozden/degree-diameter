#!/usr/bin/env python3
"""Write cubic bipartite base graphs. Format: first line b (=2h), then 3h lines 'u v' with u in [0,h) (side A), v in [h,2h) (side B).
Bases: Heawood (Fano incidence), generalized Petersen GP(n,k) with n even, k odd (bipartite), random cubic bipartite multigraphs."""
import random, sys, os
out = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'bases')
os.makedirs(out, exist_ok=True)

def write(name, h, edges):
    # edges: list of (a, b) with a in [0,h), b in [0,h) (B-side index)
    with open(os.path.join(out, name + '.txt'), 'w') as f:
        f.write(f"{2*h}\n")
        for a, b in edges: f.write(f"{a} {h+b}\n")
    print(name, 2*h, len(edges))

def gp_bip(n, k):
    # GP(n,k): outer u_i (i<n), inner v_i (i<n). Colour u_i by i%2, v_i by (i+1)%2.
    assert n % 2 == 0 and k % 2 == 1
    ua = {i: i for i in range(0, n, 2)}; ub = {}
    # side A = vertices with colour 0: u_even, v_odd ; side B = colour 1: u_odd, v_even
    A = {}; B = {}
    def vid(kind, i):
        col = (i % 2) if kind == 'u' else ((i + 1) % 2)
        d = A if col == 0 else B
        if (kind, i) not in d: d[(kind, i)] = len(d)
        return ('A' if col == 0 else 'B', d[(kind, i)])
    E = set()
    for i in range(n):
        for (x, y) in [(('u', i), ('u', (i + 1) % n)), (('u', i), ('v', i)), (('v', i), ('v', (i + k) % n))]:
            p, q = vid(*x), vid(*y)
            if p[0] == 'B': p, q = q, p
            E.add((p[1], q[1]))
    h = len(A); assert h == len(B) == n
    return h, sorted(E)

def heawood():
    E = []
    for j in range(7):
        for p in (j, (j + 1) % 7, (j + 3) % 7): E.append((p, j))
    return 7, E

def random_cubic_bip(h, rng):
    while True:
        sa = [i for i in range(h) for _ in range(3)]
        sb = [i for i in range(h) for _ in range(3)]
        rng.shuffle(sb)
        E = list(zip(sa, sb))
        # connectivity
        par = list(range(2 * h))
        def f(x):
            while par[x] != x: par[x] = par[par[x]]; x = par[x]
            return x
        for a, b in E: par[f(a)] = f(h + b)
        if len({f(x) for x in range(2 * h)}) == 1: return h, E

if __name__ == '__main__':
    write('heawood', *heawood())
    for n, k in [(8, 3), (10, 3), (12, 5), (14, 3), (14, 5), (16, 3), (16, 5), (18, 5), (20, 3), (20, 7), (24, 5), (30, 7)]:
        h, E = gp_bip(n, k); write(f'gp{n}_{k}', h, E)
    rng = random.Random(12345)
    for h in [8, 10, 12, 16, 20, 24, 30]:
        for t in range(2):
            hh, E = random_cubic_bip(h, rng); write(f'rnd{h}_{t}', hh, E)
