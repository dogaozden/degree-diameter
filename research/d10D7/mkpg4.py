"""Incidence graph of PG(2,4) as a d7hex hub graph file (K = 21, degree 5): python3 mkpg4.py out"""
import sys
# GF(4) = {0,1,w,w^2} as 0,1,2,3 with w^2 = w+1
ADD = [[a ^ b for b in range(4)] for a in range(4)]
LOG = {1: 0, 2: 1, 3: 2}
def mul(a, b):
    if a == 0 or b == 0: return 0
    return [1, 2, 3][(LOG[a] + LOG[b]) % 3]
pts = [v for v in ((a, b, c) for a in range(4) for b in range(4) for c in range(4)) if next((x for x in v if x), 0) == 1]
def dot(P, Q):
    s = 0
    for x, y in zip(P, Q): s = ADD[s][mul(x, y)]
    return s
E = [(j, k) for j, P in enumerate(pts) for k, Q in enumerate(pts) if dot(P, Q) == 0]
with open(sys.argv[1], "w") as f:
    f.write(f"{len(pts)} {len(E)}\n"); f.writelines(f"{j} {k}\n" for j, k in E)
print(len(pts), len(E))
