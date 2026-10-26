#!/usr/bin/env python3
"""Export a lift2 solution file (voltage lift of H(q) + J matchings) to an apsp edge list.
usage: export_lift.py SOLFILE HEXBIN OUT_EDGES
Vertex (x, h) of base vertex x (points 0..N-1, lines N..2N-1) and group element h has index x*m + h.
Base arc p->line with voltage g gives edges (p,h)-(N+l, h*g) for all h; matching t gives (p,h)-(N+sig(p), h*mv)."""
import struct, sys

def group_mul(spec):
    parts = spec.split()
    kind = parts[0]
    if kind == 'cyc':
        m = int(parts[1]); mul = [[(x + y) % m for y in range(m)] for x in range(m)]
    elif kind == 'prod':
        a, b = int(parts[1]), int(parts[2]); m = a * b
        mul = [[((x // b + y // b) % a) * b + (x % b + y % b) % b for y in range(m)] for x in range(m)]
    elif kind == 'dih':
        n = int(parts[1]); m = 2 * n
        mul = [[0] * m for _ in range(m)]
        for x in range(m):
            for y in range(m):
                s1, r1, s2, r2 = x // n, x % n, y // n, y % n
                r = (r1 - r2 + n) % n if s1 else (r1 + r2) % n
                mul[x][y] = ((s1 + s2) % 2) * n + r
    elif kind == 'file':
        toks = open(parts[1]).read().split(); m = int(toks[0])
        mul = [[int(toks[1 + x * m + y]) for y in range(m)] for x in range(m)]
    else:
        raise SystemExit('unknown group ' + spec)
    return m, mul

def main():
    solf, hexf, out = sys.argv[1:4]
    lines = open(solf).read().split('\n')
    q, J, m, D, cost = map(int, lines[0].split())
    spec = lines[1]
    mm, mul = group_mul(spec)
    assert mm == m, 'group order mismatch'
    sig = [list(map(int, lines[2 + t].split())) for t in range(J)]
    mv = [list(map(int, lines[2 + J + t].split())) for t in range(J)]
    hv = list(map(int, lines[2 + 2 * J].split()))
    with open(hexf, 'rb') as f:
        qq, N, L = struct.unpack('<3i', f.read(12))
        assert qq == q
        Q1 = q + 1
        pl = struct.unpack('<%di' % (N * Q1), f.read(4 * N * Q1))
    n = 2 * N * m
    edges = []
    for l in range(N):
        for k in range(Q1):
            p = pl[l * Q1 + k]; g = hv[l * Q1 + k]
            for h in range(m):
                edges.append((p * m + h, (N + l) * m + mul[h][g]))
    for t in range(J):
        for p in range(N):
            l = sig[t][p]; g = mv[t][p]
            for h in range(m):
                edges.append((p * m + h, (N + l) * m + mul[h][g]))
    # the lift may be a multigraph (a matching edge can coincide with a hexagon edge and voltage); parallel
    # copies never change distances, so the simple graph is written (dedup), and its degrees are reported
    seen = set(); simple = []
    for a, b in edges:
        key = (min(a, b), max(a, b))
        if a == b or key in seen: continue
        seen.add(key); simple.append(key)
    deg = [0] * n
    for a, b in simple: deg[a] += 1; deg[b] += 1
    with open(out, 'w') as f:
        f.write('%d\n' % n)
        f.write('\n'.join('%d %d' % e for e in simple)); f.write('\n')
    print('vertices', n, 'lift edges', len(edges), 'simple edges', len(simple), 'max degree', max(deg),
          'min degree', min(deg), 'D', D, 'cost', cost)

if __name__ == '__main__':
    main()
