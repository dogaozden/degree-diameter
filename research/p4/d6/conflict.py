"""Conflict graph of whisker candidates (lines opposite v not in S; conflict = share a point off S) for ils_mis.
Usage: conflict.py q seed out.txt -> writes graph and out.txt.ids (candidate line ids)"""
import sys, collections
from hexbin import load
q, seed, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
_, N, lines, crd = load(q); lines = lines.tolist()
S = [int(x) for x in open(f'runs/S_q{q}_s{seed}.txt').read().split()]; v = S[0]; Sset = set(S)
spt = {p for s in S for p in lines[s]}
thr = [[] for _ in range(N)]
for k, L in enumerate(lines):
    for p in L: thr[p].append(k)
vl = set(k for p in lines[v] for k in thr[p])
blocked = set(p for k in vl for p in lines[k]) - spt
cand = [k for k in range(len(lines)) if k not in Sset and k not in vl and not any(p in blocked for p in lines[k])]
idx = {k: i for i, k in enumerate(cand)}
E = set()
for p in range(N):
    if p in spt or p in blocked: continue
    cs = [idx[k] for k in thr[p] if k in idx]
    for a in cs:
        for b in cs:
            if a < b: E.add((a, b))
with open(out, 'w') as f:
    f.write(f'{len(cand)} {len(E)}\n')
    for a, b in sorted(E): f.write(f'{a} {b}\n')
open(out + '.ids', 'w').write('\n'.join(map(str, cand)) + '\n')
print(len(cand), len(E))
