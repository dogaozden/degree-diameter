"""Write the whisker exact-cover instance for wsa.c: for each spread point of an A-line (spread lines outside B and
v), its candidate whiskers (line id + free-point indices). Usage: wprep.py q seed Bfile out.txt"""
import collections, sys
from hexbin import load

q, seed, bfile, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], sys.argv[4]
_, N, lines, crd = load(q)
lines = lines.tolist()
S = [int(x) for x in open(f'runs/S_q{q}_s{seed}.txt').read().split()]
v = S[0]
B = set(int(x) for x in open(bfile).read().split()) if bfile != '-' else set()
Sset = set(S)
spt = {p: s for s in S for p in lines[s]}
thr = [[] for _ in range(N)]
for k, L in enumerate(lines):
    for p in L:
        thr[p].append(k)
vlines = set(k for p in lines[v] for k in thr[p])
blocked = set(p for k in vlines for p in lines[k]) - set(spt)
free = [p for p in range(N) if p not in spt and p not in blocked]
fid = {p: i for i, p in enumerate(free)}
Apts = [p for s in S if s != v and s not in B for p in lines[s]]
with open(out, 'w') as f:
    f.write(f'{q} {len(free)} {len(Apts)}\n')
    for p in Apts:
        opts = []
        for k in thr[p]:
            if k in Sset or k in vlines or any(x in blocked for x in lines[k]):
                continue
            opts.append([k] + [fid[x] for x in lines[k] if x != p])
        f.write(f'{len(opts)}\n')
        for o in opts:
            f.write(' '.join(map(str, o)) + '\n')
print('free', len(free), 'A-points', len(Apts))
