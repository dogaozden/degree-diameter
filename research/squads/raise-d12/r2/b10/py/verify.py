# independent verifier: reads a haar_sl8d solution file, builds H(G,S) from scratch in Python and writes an edge list
# usage: python3 -I verify.py SOL.txt EDGES.txt   (then run apsp EDGES Delta 12)
import sys
sys.path.insert(0, "/home/user/degree-diameter/research/squads/raise-d12/r2/b10/py")
from grp import SL, gm, F
P = None; S = []
for line in open(sys.argv[1]):
    t = line.split()
    if not t or t[0] == '#': continue
    if t[0] == 'P': P = int(t[1]); U = int(t[3])
    if t[0] == 'S':
        a, b, c, d, x, j = map(int, t[1:7]); S.append(((a, b, c, d), (x, j)))
assert P and S
G = [(M, (x, j)) for M in SL for x in range(P) for j in (0, 1)]
idx = {g: i for i, g in enumerate(G)}
n = len(G)
assert n * 2 <= 2000000
edges = set()
for g in G:
    for s in S:
        h = gm(s, g, P)
        u = idx[g]; v = n + idx[h]
        edges.add((min(u, v), max(u, v)))
edges = sorted(edges)
with open(sys.argv[2], 'w') as f:
    f.write(f"{2*n}\n")
    for u, v in edges: f.write(f"{u} {v}\n")
print("N", n, "vertices", 2*n, "edges", len(edges), "S size", len(S), "distinct", len(set(S)))
