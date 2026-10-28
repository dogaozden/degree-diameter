"""Typed level layouts (Section 6 of D5_QUADRANGLE.md): over all regular tournaments on 2r+1 levels (up to relabelling,
by brute force for r <= 3; rotational tournaments for r = 4) and all H/D typings, maximise K_A + K_B where
K_B = min_j sum of caps of arcs leaving j, K_A = min_j sum of caps of arcs entering j.
caps: H->D (points of the H-quadrangle freed): a; D->H (lines freed): b; H->H and D->D: c."""
import itertools, sys

def regular_tournaments(n):
    pairs = list(itertools.combinations(range(n), 2)); r = (n - 1) // 2
    seen = set(); out = []
    for bits in range(1 << len(pairs)):
        od = [0] * n; arcs = []
        for i, (u, v) in enumerate(pairs):
            if bits >> i & 1: od[u] += 1; arcs.append((u, v))
            else: od[v] += 1; arcs.append((v, u))
        if all(d == r for d in od):
            out.append(arcs)
    return out

def rotational(n, conn):
    return [(j, (j + k) % n) for j in range(n) for k in conn]

def best(arcsets, n, a, b, c):
    res = []
    for arcs in arcsets:
        for types in itertools.product('HD', repeat=n):
            def cap(u, v):
                if types[u] == 'H' and types[v] == 'D': return a
                if types[u] == 'D' and types[v] == 'H': return b
                return c
            out = [0] * n; inn = [0] * n
            for (u, v) in arcs:
                w = cap(u, v); out[u] += w; inn[v] += w
            KB, KA = min(out), min(inn)
            res.append((KA + KB, KA, KB, ''.join(types), arcs))
    res.sort(key=lambda x: -x[0])
    return res[0]

if __name__ == '__main__':
    for n in (3, 5, 7):
        T = regular_tournaments(n) if n <= 7 else None
        print('n=%d: %d labelled regular tournaments' % (n, len(T)))
        for (a, b, c) in [(1, 1, 0), (122, 111, 0), (122, 111, 2), (122, 100, 2), (82, 73, 2), (82, 60, 2), (122, 111, 10)]:
            s, KA, KB, ty, arcs = best(T, n, a, b, c)
            print('  a=%d b=%d c=%d: best K_A+K_B=%d (K_A=%d, K_B=%d) types %s arcs %s' % (a, b, c, s, KA, KB, ty, sorted(arcs)))
