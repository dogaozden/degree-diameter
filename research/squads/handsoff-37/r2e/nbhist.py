"""Histogram of the raw lift cost over the full 1-move neighbourhood of a C_N k-lift state (lift2 INIT format).
usage: nbhist.py GROUPFILE STATE"""
import sys
from collections import Counter
def load_group(path):
    t = open(path).read().split(); N = int(t[0])
    mul = [[int(t[1 + a * N + b]) for b in range(N)] for a in range(N)]
    inv = [0] * N
    for a in range(N):
        for b in range(N):
            if mul[a][b] == 0: inv[a] = b
    return N, mul, inv
def cost(k, N, mul, inv, eu, ev, ea, D=7):
    n = 2 * k * N
    nb = [[0, 0, 0] for _ in range(n)]
    wv = [[] for _ in range(k)]; bu = [[] for _ in range(k)]
    for e in range(len(eu)):
        wv[eu[e]].append((ev[e], ea[e])); bu[ev[e]].append((eu[e], inv[ea[e]]))
    for u in range(k):
        for g in range(N):
            for j, (v, a) in enumerate(wv[u]):
                nb[u * N + g][j] = (k + v) * N + mul[g][a]
    for v in range(k):
        for h in range(N):
            for j, (u, a) in enumerate(bu[v]):
                nb[(k + v) * N + h][j] = u * N + mul[h][a]
    R = [0] * n
    for s in range(2 * k): R[s * N] = 1 << s
    full = (1 << (2 * k)) - 1
    for _ in range(D):
        R = [R[x] | R[nb[x][0]] | R[nb[x][1]] | R[nb[x][2]] for x in range(n)]
    c = 0
    for x in range(n):
        c += bin(~R[x] & full).count('1')
    dup = 0
    E = len(eu)
    for e in range(E):
        for f in range(e + 1, E):
            if eu[e] == eu[f] and ev[e] == ev[f] and ea[e] == ea[f]: dup += 1
    return c, dup
if __name__ == '__main__':
    N, mul, inv = load_group(sys.argv[1])
    L = open(sys.argv[2]).read().split()
    k = int(L[1]); E = 3 * k
    eu = [int(L[2 + 3 * i]) for i in range(E)]; ev = [int(L[3 + 3 * i]) for i in range(E)]; ea = [int(L[4 + 3 * i]) for i in range(E)]
    c0, d0 = cost(k, N, mul, inv, eu, ev, ea)
    print('base cost', c0, 'dup', d0)
    hv = Counter(); h2 = Counter()
    for e in range(E):
        for a in range(N):
            if a == ea[e]: continue
            ea2 = ea[:]; ea2[e] = a
            c, d = cost(k, N, mul, inv, eu, ev, ea2)
            hv[c] += 1
    for e in range(E):
        for f in range(e + 1, E):
            if ev[e] == ev[f]: continue
            ev2 = ev[:]; ev2[e], ev2[f] = ev2[f], ev2[e]
            c, d = cost(k, N, mul, inv, eu, ev2, ea)
            h2[c] += 1
    print('voltage moves: min', min(hv), 'counts by cost (first 15 keys)', sorted(hv.items())[:15])
    print('2-switch moves: min', min(h2), 'counts by cost (first 15 keys)', sorted(h2.items())[:15])
