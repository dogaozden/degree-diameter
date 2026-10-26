# independent check: rebuild the coset graph for the first (group, pair) by definition and compare
import sys, itertools, random
from collections import deque
toks = open(sys.argv[1]).read().split('\n')
i = 0
def parse():
    global i
    groups = []
    while i < len(toks):
        line = toks[i].split()
        if not line: i += 1; continue
        if line[0] == 'GROUP':
            n = int(line[1]); idx = int(line[2]); i += 1
            M = [list(map(int, toks[i+r].split())) for r in range(n)]; i += n
            pairs = []
            while i < len(toks) and toks[i].startswith('PAIR'):
                _, a, b, k = toks[i].split(); i += 1
                dcs = []
                for _ in range(int(k)):
                    v = list(map(int, toks[i].split())); i += 1
                    dcs.append(v[1:])
                pairs.append((int(a), int(b), dcs))
            groups.append((n, idx, M, pairs))
        else:
            i += 1
    return groups
G = parse()
n, idx, M, pairs = G[0]
inv = [M[x].index(0) for x in range(n)]
def mul(x, y): return M[x][y]
def graph(a, b, D):
    # white cosets {x, xa}, black {y, yb}; x~y iff x^-1 y in D
    Dset = set(D)
    wl = {}; bl = {}
    wc = []; bc = []
    for x in range(n):
        if x not in wl:
            wl[x] = len(wc); wl[mul(x,a)] = len(wc); wc.append(x)
    for y in range(n):
        if y not in bl:
            bl[y] = len(bc); bl[mul(y,b)] = len(bc); bc.append(y)
    N = len(wc)
    adj = [set() for _ in range(2*N)]
    for w, x in enumerate(wc):
        for y in range(n):
            if mul(inv[x], y) in Dset:
                bb = bl[y]
                adj[w].add(N+bb); adj[N+bb].add(w)
    return adj, N
def bfs(adj, s):
    d = [-1]*len(adj); d[s] = 0; q = deque([s])
    while q:
        v = q.popleft()
        for u in adj[v]:
            if d[u] < 0: d[u] = d[v]+1; q.append(u)
    return d
a, b, dcs = pairs[0]
print('group', n, idx, 'pair', a, b, 'ndc', len(dcs), 'sizes', sorted(set(len(d) for d in dcs)))
S = [d for d in dcs if len(d) == 2]; F = [d for d in dcs if len(d) == 4]
cands = []
for f in F:
    for s in S: cands.append(f+s)
for t in itertools.combinations(S, 3): cands.append(sum(t, []))
random.seed(1)
best = None
sample = cands if len(cands) <= 300 else random.sample(cands, 300)
res = []
for D in sample:
    adj, N = graph(a, b, D)
    if any(len(x) != 3 for x in adj): print('degree problem'); continue
    d0 = bfs(adj, 0); dB = bfs(adj, N)
    if min(d0) < 0: res.append(None); continue
    cW = sum(1 for v in range(N) if d0[v] > 6); cB = sum(1 for v in range(N, 2*N) if dB[v] > 6)
    cost = (N*cW + N*cB)//2
    diam = max(max(d0), max(dB))
    res.append((cost, diam))
conn = [r for r in res if r]
print('sampled', len(sample), 'connected', len(conn), 'min cost', min(conn)[0] if conn else None, 'min diam', min(r[1] for r in conn) if conn else None)
