import sys
from collections import deque
m, k, r = 5023, 31, 2886
assert pow(r, k, m) == 1
N = m * k
S = []
for line in open(sys.argv[1]).read().split('\n')[1:]:
    p = line.split()
    if len(p) >= 2 and p[0].isdigit() and p[1].startswith('meta'):
        S.append(int(p[0]))
print('|S| =', len(S), 'N =', N)
def mul(x, y):
    a1, j1 = divmod(x, k); a2, j2 = divmod(y, k)
    return ((a1 + pow(r, j1, m) * a2) % m) * k + (j1 + j2) % k
Lmul = {}
Sinv = {}
for s in S:
    Sinv[s] = [t for t in range(N) if mul(s, t) == 0][0]; Lmul[s] = [mul(s, g) for g in range(N)]; Lmul[Sinv[s]] = [mul(Sinv[s], g) for g in range(N)]
def bfs(src_side):
    V = 2 * N
    dist = [-1] * V
    start = src_side * N
    dist[start] = 0
    q = deque([start])
    while q:
        v = q.popleft(); d = dist[v]
        side, g = divmod(v, N)
        if side == 0:
            nbrs = [N + Lmul[s][g] for s in S]
        else:
            nbrs = [Lmul[Sinv[s]][g] for s in S]
        for w in nbrs:
            if dist[w] < 0:
                dist[w] = d + 1; q.append(w)
    return max(dist), dist.count(-1)
ea, ua = bfs(0); eb, ub = bfs(1)
print('ecc A', ea, 'unreached', ua, '| ecc B', eb, 'unreached', ub)
print('diameter from (e,A),(e,B) =', max(ea, eb), 'vertices', 2 * N)
