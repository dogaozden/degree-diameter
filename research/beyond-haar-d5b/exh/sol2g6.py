#!/usr/bin/env python3
"""graph6 lines for b4a2x/b4a2y solution lines (lift of [[2,3],[3,2]], same conventions as b4a2x_edges.py).
usage: sol2g6.py GROUP SOLFILE > out.g6   (pipe into nauty-shortg to count isomorphism classes)"""
import sys
f = open(sys.argv[1]).read().split(); m = int(f[0]); mul = [[int(f[1 + i * m + j]) for j in range(m)] for i in range(m)]
def g6(n, E):
    adj = [[0] * n for _ in range(n)]
    for u, v in E: adj[u][v] = adj[v][u] = 1
    bits = [adj[i][j] for j in range(1, n) for i in range(j)]
    bits += [0] * (-len(bits) % 6)
    out = chr(63 + n) if n < 63 else '~' + ''.join(chr(63 + ((n >> s) & 63)) for s in (12, 6, 0))
    return out + ''.join(chr(63 + int(''.join(map(str, bits[i:i + 6])), 2)) for i in range(0, len(bits), 6))
for line in open(sys.argv[2]):
    t = line.split()
    if not t or t[0] != 'SOL': continue
    x = int(t[2]); y1, y2 = int(t[4]), int(t[5]); z = [int(t[7]), int(t[8]), int(t[9])]; w = int(t[11])
    base = [(0, 2, 0), (0, 2, x), (0, 3, 0), (0, 3, y1), (0, 3, y2)] + [(1, 2, g) for g in z] + [(1, 3, 0), (1, 3, w)]
    E = set((a * m + h, b * m + mul[h][g]) for a, b, g in base for h in range(m))
    assert len(E) == 10 * m
    print(g6(4 * m, E))
