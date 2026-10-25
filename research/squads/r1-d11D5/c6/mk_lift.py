# Writes base-edge file (base.txt: "u v" per edge, u in side A) and lift files for liftcheck.
# usage: mk_lift.py base|lift <seed> <M> <out>
import json, sys, random
mode = sys.argv[1]
d = json.load(open('/home/user/degree-diameter/research/gq4x/graphs/as_w2_q9_n1782.json'))
E = d['output'][1]; n = 1782
side = list(map(int, open('side.txt').read().split())) if False else None
import numpy as np
side = np.load('side.npy').astype(int).tolist()
idxA = {}; idxB = {}
for v in range(n):
    if side[v] == 0: idxA[v] = len(idxA)
    else: idxB[v] = len(idxB)
edges = []
for u, v in E:
    a, b = (u, v) if side[u] == 0 else (v, u)
    edges.append((a, b))
if mode == 'base':
    with open(sys.argv[4], 'w') as f:
        for a, b in edges: f.write(f"{a} {b}\n")
else:
    seed = int(sys.argv[2]); M = int(sys.argv[3]); rnd = random.Random(seed)
    with open(sys.argv[4], 'w') as f:
        f.write(f"{len(idxA)} {len(idxB)} {M}\n")
        for a, b in edges:
            f.write(f"{idxA[a]} {idxB[b]} {rnd.randrange(M)}\n")
