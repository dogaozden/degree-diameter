# Moore-base wall: base = incidence graph of H(2) (Tutte 12-cage), read from r1/a01/code/base_edges.txt.
# Non-backtracking walks of length <= 12; cotree edges carry voltages; walk c-vector = signed cotree counts.
import sys, random
from collections import deque, Counter
import numpy as np
F = '/home/user/degree-diameter/research/squads/raise-d12/r1/a01/code/base_edges.txt'
lines = open(F).read().split('\n')
n, E = map(int, lines[0].split())
edges = []
for ln in lines[1:1 + E]:
    p, l, t = map(int, ln.split()); edges.append((p, l, t))
adj = [[] for _ in range(n)]
cot = []  # cotree edge index for each edge (or -1)
for idx, (p, l, t) in enumerate(edges):
    adj[p].append((l, idx)); adj[l].append((p, idx))
ci = 0; cidx = {}
for idx, (p, l, t) in enumerate(edges):
    if t == 0: cidx[idx] = ci; ci += 1
NC = ci  # 64
# checks: diameter, girth-12 via BFS, bipartite
def bfs(s):
    d = [-1] * n; d[s] = 0; dq = deque([s])
    while dq:
        x = dq.popleft()
        for y, _ in adj[x]:
            if d[y] < 0: d[y] = d[x] + 1; dq.append(y)
    return d
diam = max(max(bfs(s)) for s in range(n))
print('vertices', n, 'edges', E, 'cotree', NC, 'diameter', diam, flush=True)

LMAX = 12
# enumerate nb walks from each source: returns list of (end, length, sparse signed cotree vector as tuple of (cidx,sign))
def walks_from(u):
    res = []
    stack = [(u, -1, 0, ())]  # (vertex, prev vertex, length, vec)
    while stack:
        x, prev, L, vec = stack.pop()
        res.append((x, L, vec))
        if L == LMAX: continue
        for y, idx in adj[x]:
            if y == prev: continue
            sgn = 1 if x < y else -1   # direction point->line is +1 (point index < 63 <= line index)
            v2 = vec + ((cidx[idx], sgn),) if idx in cidx else vec
            stack.append((y, x, L + 1, v2))
    return res

if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'counts'
    u = 0
    W = walks_from(0)
    cnt = Counter(); lenc = Counter()
    for (x, L, vec) in W:
        cnt[(x >= 63, L)] += 1
    # per target count (point source 0): lines get walks of odd length <= 11; points even <= 12
    perline = Counter(x for (x, L, vec) in W if x >= 63 and L <= 11)
    perpt = Counter(x for (x, L, vec) in W if x < 63 and L <= 12)
    print('source point 0: total nb walks length<=12:', len(W))
    print('walks to each line (length<=11): min', min(perline[v] for v in range(63, 126)), 'max', max(perline[v] for v in range(63, 126)), flush=True)
    print('walks to each point (length<=12) incl. source: min', min(perpt[v] for v in range(0, 63)), 'max', max(perpt[v] for v in range(0, 63)), flush=True)
    # distinct c-vectors among walks from point 0 to each line of length <= 11
    dist_c = []
    for L_ in range(63, 126):
        vecs = []
        for (x, Lw, vec) in W:
            if x == L_ and Lw <= 11:
                d = {}
                for c, s in vec: d[c] = d.get(c, 0) + s
                vecs.append(tuple(sorted((c, s) for c, s in d.items() if s)))
        dist_c.append((len(vecs), len(set(vecs))))
    print('per line: (walks, distinct c-vectors) min/max:', min(dist_c), max(dist_c), flush=True)
    # rank over Q of the 65 c-vectors to one line (point 0 -> line 63)
    def mat(L_):
        M = []
        for (x, Lw, vec) in W:
            if x == L_ and Lw <= 11:
                row = np.zeros(NC)
                for c, s in vec: row[c] += s
                M.append(row)
        return np.array(M)
    for L_ in (63, 64, 100):
        M = mat(L_)
        print('line', L_, 'rank over Q of walk c-vectors:', np.linalg.matrix_rank(M), 'of', len(M), flush=True)
