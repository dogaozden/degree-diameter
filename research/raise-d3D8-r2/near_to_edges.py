"""NEAR line (tlift NEARFILE) -> lift edge file for sa_repair.  Usage: near_to_edges.py GROUPFILE BASEFILE NEARLINE_INDEX OUT
Reads the group table of the group named in the NEAR line, the base (k E, edges x y, x white), the voltage list."""
import sys, re
sys.path.insert(0, '.')
from verify_tl import load_group
gfile, bfile, idx, outp = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
line = [l for l in open('near/near4_73_90.txt') if l.startswith('NEAR')][idx]
t = line.split()
n_, g_ = int(t[2]), int(t[4])
volt = [int(x) for x in t[t.index('volt') + 1:]]
N, M, inv = load_group(gfile, n_, g_)
L = open(bfile).read().split('\n')
k, E = map(int, L[0].split())
edges = [tuple(map(int, l.split())) for l in L[1:1 + E]]
# colour by BFS from 0 (same convention as tlift: white = colour 0)
col = {0: 0}; q = [0]
while q:
    u = q.pop()
    for x, y in edges:
        for a, b in ((x, y), (y, x)):
            if a == u and b not in col:
                col[b] = 1 - col[u]; q.append(b)
E2 = []
for (x, y), a in zip(edges, volt):
    if col[x] == 1: x, y = y, x
    E2.append((x, y, a))
lift = []
for x, y, a in E2:
    for g in range(N):
        lift.append((x * N + g, y * N + M[a][g]))
with open(outp, 'w') as o:
    o.write(f"{k*N} {len(lift)}\n")
    for u, v in lift: o.write(f"{u} {v}\n")
print("n", k*N, "edges", len(lift), "cost-line", line.strip()[:60])
