import sys
sys.argv = ['x', 'g170.txt']
exec(open('check.py').read().split("a, b, dcs = pairs[0]")[0])
a, b, dcs = pairs[0]
S = [d for d in dcs if len(d) == 2]; F = [d for d in dcs if len(d) == 4]
cands = []
for f in F:
    for s in S: cands.append(f+s)
import itertools
for t in itertools.combinations(range(len(S)), 3): cands.append(sum([S[k] for k in t], []))
from collections import deque
bad = 0; checked = 0
for line in open('dbg11.txt'):
    p = line.split()
    opt = int(p[4][3:]); ccost = int(p[6]); cdiam = int(p[8])
    D = cands[opt]
    adj, N = graph(a, b, D)
    d0 = bfs(adj, 0); dB = bfs(adj, N)
    if min(d0) < 0: pcost = None
    else:
        cW = sum(1 for v in range(N) if d0[v] > 6); cB = sum(1 for v in range(N, 2*N) if dB[v] > 6)
        pcost = (N*cW + N*cB)//2; pdiam = max(max(d0), max(dB))
    checked += 1
    if pcost != ccost: bad += 1; print('mismatch opt', opt, ccost, pcost)
    if checked >= 60: break
print('checked', checked, 'mismatches', bad)
