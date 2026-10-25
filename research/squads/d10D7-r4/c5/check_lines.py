import sys, numpy as np
from collections import Counter
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D7-r4/c5')
from hexio import *
q, N, lines, coords = load_hex('/home/user/degree-diameter/research/d10D7/hex/hex_q7.bin')
pl = point_lines(q, N, lines)
L = lines.shape[0]
def rank2(a, b, c, d):   # rank of [[a,b],[c,d]] mod 7 (0,1,2)
    det = (a*d - b*c) % 7
    if det: return 2
    if (a % 7) or (b % 7) or (c % 7) or (d % 7): return 1
    return 0
def line_opp_crit(l, m):
    x1, x2 = coords[lines[l][0]], coords[lines[l][1]]
    y1, y2 = coords[lines[m][0]], coords[lines[m][1]]
    return rank2(bform(x1, y1, q), bform(x1, y2, q), bform(x2, y1, q), bform(x2, y2, q)) == 2
agree = 0; tot = 0; hist = Counter()
rng = np.random.default_rng(1)
for src in [0, 5000, 12345]:
    _, dl = bfs_dist(q, N, lines, pl, N + 0 if False else 0)  # placeholder (overwritten below)
    # BFS from line src: build dist over lines
    dist = np.full(N + L, -1, dtype=np.int64)
    dist[N + src] = 0; fr = [N + src]; d = 0
    while fr:
        d += 1; nx = []
        for v in fr:
            if v < N:
                for l in pl[v]:
                    if dist[N + l] < 0: dist[N + l] = d; nx.append(N + l)
            else:
                for p in lines[v - N]:
                    if dist[p] < 0: dist[p] = d; nx.append(p)
        fr = nx
    dlines = dist[N:]
    hist.update(Counter(dlines.tolist()))
    for m in range(L):
        if m == src: continue
        pred = line_opp_crit(src, m)
        bfs_opp = (dlines[m] == 6)
        tot += 1; agree += (pred == bfs_opp)
print('line-line distance hist (src 0,5000,12345 summed):', sorted(hist.items()))
print('criterion det!=0 agrees with BFS distance 6:', agree, 'of', tot)
