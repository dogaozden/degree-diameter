"""Candidate whiskers (lines opposite v not in S) with their free points, for wsa2.c.
Usage: cprep.py q seed out.txt   (format: nfree ncand q, then per candidate: line_id r_1..r_q)"""
import sys
from hexbin import load
q, seed, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
_, N, lines, crd = load(q); lines = lines.tolist()
S = [int(x) for x in open(f'runs/S_q{q}_s{seed}.txt').read().split()]; v = S[0]; Sset = set(S)
onS = bytearray(N)
for s in S:
    for p in lines[s]: onS[p] = 1
thr = [[] for _ in range(N)]
for k, L in enumerate(lines):
    for p in L: thr[p].append(k)
vl = set(k for p in lines[v] for k in thr[p])
blocked = bytearray(N)
for k in vl:
    for p in lines[k]:
        if not onS[p]: blocked[p] = 1
fid = {}
for p in range(N):
    if not onS[p] and not blocked[p]: fid[p] = len(fid)
cand = [k for k in range(len(lines)) if k not in Sset and k not in vl and not any(blocked[p] for p in lines[k])]
with open(out, 'w') as f:
    f.write(f'{len(fid)} {len(cand)} {q}\n')
    for k in cand:
        f.write(str(k) + ' ' + ' '.join(str(fid[p]) for p in lines[k] if not onS[p]) + '\n')
print(len(fid), len(cand))
