#!/usr/bin/env python3
"""Edge list of a lift of a 2+2 base from a solution line of b4a2y/b4a2x ("SOL x .. y .. .. z .. .. .. w ..", base
[[2,3],[3,2]]) or b4a1x ("SOL g a b c d e f h c k", base [[1,4],[4,1]]: A0-B0 {1}, A0-B1 {1, g..}, A1-B0 {1, d..},
A1-B1 {c}). Base vertices A0, A1, B0, B1 = 0..3, edges oriented A -> B; lift vertex (v, h) = v*m + h, and a base
edge a -> b of voltage g gives (a, h) ~ (b, h*g).   usage: lift_edges.py GROUP "SOL ..." OUT.edges"""
import sys
f = open(sys.argv[1]).read().split(); m = int(f[0]); mul = [[int(f[1 + i * m + j]) for j in range(m)] for i in range(m)]
t = sys.argv[2].split()
if t[1] == 'x':
    x = int(t[2]); y1, y2 = int(t[4]), int(t[5]); z = [int(t[7]), int(t[8]), int(t[9])]; w = int(t[11])
    base = [(0, 2, 0), (0, 2, x), (0, 3, 0), (0, 3, y1), (0, 3, y2)] + [(1, 2, g) for g in z] + [(1, 3, 0), (1, 3, w)]
else:
    i = t.index('g'); j = t.index('d'); k = t.index('c')
    g = [int(v) for v in t[i + 1:j]]; d = [int(v) for v in t[j + 1:k]]; c = int(t[k + 1])
    # b4a1x prints g2 g3 g4 and d2 d3 d4 (the identity 0 is the fourth voltage of each class)
    base = [(0, 2, 0)] + [(0, 3, v) for v in [0] + g] + [(1, 2, v) for v in [0] + d] + [(1, 3, c)]
assert len(base) == 10, base
E = set()
for a, b, g in base:
    for h in range(m):
        e = (a * m + h, b * m + mul[h][g]); assert e not in E, "multi-edge"; E.add(e)
with open(sys.argv[3], 'w') as o:
    o.write(f"{4 * m}\n")
    for u, v in sorted(E): o.write(f"{u} {v}\n")
print(len(E), "edges,", 4 * m, "vertices", file=sys.stderr)
