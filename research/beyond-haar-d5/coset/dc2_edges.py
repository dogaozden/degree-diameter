#!/usr/bin/env python3
"""Edge list of a bi-coset graph from a .dc2 file and a set of double-coset ids; edges of the ids listed after
'--movable' get a third column 1 (for ga MOVABLE mode).  usage: dc2_edges.py FILE.dc2 OUT ids... [--movable ids...]"""
import sys
f, out = sys.argv[1], sys.argv[2]
args = sys.argv[3:]
mov = set()
if '--movable' in args:
    i = args.index('--movable'); mov = set(map(int, args[i + 1:])); args = args[:i]
ids = list(map(int, args)) + sorted(mov)
tok = open(f).read().split(); p = 0
def nxt():
    global p; p += 1; return int(tok[p - 1])
nA, nB, ng, ndc = nxt(), nxt(), nxt(), nxt()
gA, gB = [], []
for s in range(ng):
    gA.append([nxt() for _ in range(nA)]); gB.append([nxt() for _ in range(nB)])
dcs = []
for d in range(ndc):
    c = nxt(); dcs.append([nxt() for _ in range(c)])
permB = {0: list(range(nB))}; q = [0]
while q:
    a = q.pop(0)
    for s in range(ng):
        a2 = gA[s][a]
        if a2 in permB: continue
        permB[a2] = [gB[s][permB[a][b]] for b in range(nB)]; q.append(a2)
E = []
for d in ids:
    for a in range(nA):
        for b0 in dcs[d]:
            E.append((a, nA + permB[a][b0], 1 if d in mov else 0))
with open(out, 'w') as fo:
    fo.write(f"{nA + nB}\n")
    for a, b, m in E: fo.write(f"{a} {b} {m}\n" if mov else f"{a} {b}\n")
print("contributions", [len(dcs[d]) for d in ids], "edges", len(E))
