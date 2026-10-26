#!/usr/bin/env python3
"""Independent checker for 2-fiber bi-Cayley lifts written by bicay.c (shares no code with the C evaluator).

usage: verify.py GROUP.bin CONFIG.txt [--full]
Builds the explicit graph (4|G| vertices, degree d), checks simplicity, degree, bipartiteness,
and computes the diameter: BFS from the 4 fiber roots (exact, because G acts on each fiber), or
with --full a BFS from every vertex.
"""
import sys, struct
from collections import deque
import numpy as np

def load_group(path):
    data = open(path, 'rb').read()
    h = struct.unpack('<I', data[:4])[0]
    MH = np.frombuffer(data[4:], dtype='<u2').reshape(h, h).astype(np.int64)
    INV = [int(np.where(MH[a] == 0)[0][0]) for a in range(h)]
    return h, MH, INV

def load_config(path):
    lines = open(path).read().strip().split('\n')
    hdr = lines[0].split()
    p = {hdr[i]: hdr[i + 1] for i in range(0, len(hdr) - 1, 2)}
    n, A, d, D = int(p['n']), int(p['A']), int(p['d']), int(p['D'])
    blocks = {}
    for line in lines[1:5]:
        parts = line.split()
        blocks[parts[0]] = [int(x) for x in parts[1:]]
    return n, A, d, D, blocks, p.get('GROUP')

def build(h, MH, INV, n, blocks):
    """vertex id = ((side*2 + fiber)*h + row)*n + z ; edges (g,0,i) ~ (a g,1,j) for a in S_ij."""
    S = {(i, j): blocks['S%d%d' % (i, j)] for i in (0, 1) for j in (0, 1)}
    V = 4 * h * n
    adj = [[] for _ in range(V)]
    def vid(side, fib, row, z):
        return ((side * 2 + fib) * h + row) * n + z
    for i in (0, 1):
        for j in (0, 1):
            for code in S[(i, j)]:
                a, c = divmod(code, n)
                for row in range(h):
                    for z in range(n):
                        u = vid(0, i, row, z)
                        v = vid(1, j, int(MH[a, row]), (z + c) % n)
                        adj[u].append(v); adj[v].append(u)
                        # reverse edges are added above; the side-1 side needs no extra loop
    return adj

def check_structure(adj, d):
    V = len(adj)
    for u in range(V):
        if len(adj[u]) != d:
            return 'degree %d at %d' % (len(adj[u]), u)
        if len(set(adj[u])) != d:
            return 'multi-edge at %d' % u
    return None

def bfs_ecc(adj, src):
    dist = [-1] * len(adj)
    dist[src] = 0
    q = deque([src])
    while q:
        u = q.popleft()
        for v in adj[u]:
            if dist[v] < 0:
                dist[v] = dist[u] + 1
                q.append(v)
    return dist

def main():
    grp, cfg = sys.argv[1], sys.argv[2]
    full = '--full' in sys.argv
    h, MH, INV = load_group(grp)
    n, A, d, D, blocks, gname = load_config(cfg)
    adj = build(h, MH, INV, n, blocks)
    err = check_structure(adj, d)
    print('structure:', 'OK (simple, %d-regular, %d vertices)' % (d, len(adj)) if err is None else 'FAIL ' + err)
    if err: return
    # bipartite: side of vertex = (id // (h*n)) // 2 ; every edge must join sides 0 and 1
    V = len(adj); per = h * n
    bip = all(((u // per) // 2) != ((v // per) // 2) for u in range(V) for v in adj[u])
    print('bipartite:', bip)
    roots = [0, per, 2 * per, 3 * per]          # identity of each fiber (row 0, z 0)
    if full:
        diam = 0
        for src in range(V):
            dist = bfs_ecc(adj, src)
            if min(dist) < 0: diam = 10**9; break
            diam = max(diam, max(dist))
        print('full APSP diameter:', diam, '(need <= %d)' % D)
        return
    cost = 0; diam = 0
    for r in roots:
        dist = bfs_ecc(adj, r)
        cost += sum(1 for x in dist if x < 0 or x > D)
        diam = max(diam, max(dist) if min(dist) >= 0 else 10**9)
    print('cost (uncovered within D, 4 roots): %d   root-ecc max: %s' % (cost, diam))

if __name__ == '__main__':
    main()
