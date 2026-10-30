#!/usr/bin/env python3
"""Edge list of a b4a2x solution: lift of the 2+2 base [[2,3],[3,2]] by a group (multiplication table, identity 0).
Base A0, A1 (side A), B0, B1 (side B); edges A0-B0 {1, x}, A0-B1 {1, y1, y2}, A1-B0 {z0, z1, z2}, A1-B1 {1, w},
oriented A -> B. Lift: (a, h) ~ (b, h*g). Vertex (v, h) has index v*m + h (A0, A1, B0, B1 = 0, 1, 2, 3).
usage: b4a2x_edges.py GROUP "SOL x .. y .. .. z .. .. .. w .." OUT.edges"""
import sys
f = open(sys.argv[1]).read().split(); m = int(f[0]); mul = [[int(f[1 + i * m + j]) for j in range(m)] for i in range(m)]
t = sys.argv[2].split(); x = int(t[2]); y1, y2 = int(t[4]), int(t[5]); z = [int(t[7]), int(t[8]), int(t[9])]; w = int(t[11])
base = [(0, 2, 0), (0, 2, x), (0, 3, 0), (0, 3, y1), (0, 3, y2)] + [(1, 2, g) for g in z] + [(1, 3, 0), (1, 3, w)]
E = set()
for a, b, g in base:
    for h in range(m):
        e = (a * m + h, b * m + mul[h][g])
        assert e not in E, "multi-edge"
        E.add(e)
with open(sys.argv[3], 'w') as o:
    o.write(f"{4 * m}\n")
    for u, v in sorted(E): o.write(f"{u} {v}\n")
print(len(E), "edges,", 4 * m, "vertices")
