"""onefactor.py q j out [seed] [m]: write a lift solution file whose j matchings are edge-disjoint 1-factors of the
hexagon H(q) (tau_t(p) is a line through p), i.e. doubled flags, with random voltages in Z_m (or all zero if m=0).
1-factors from a random proper edge colouring: repeatedly take a perfect matching (Hopcroft-Karp on a random edge
order) of the remaining regular bipartite graph."""
import random, struct, sys
from collections import deque

q, j, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
seed = int(sys.argv[4]) if len(sys.argv) > 4 else 1
m = int(sys.argv[5]) if len(sys.argv) > 5 else 4
random.seed(seed)
with open(f'hex/hex_q{q}.bin', 'rb') as f:
    qq, N, L = struct.unpack('3i', f.read(12))
    Q1 = q + 1
    lines = [list(struct.unpack(f'{Q1}i', f.read(4 * Q1))) for _ in range(L)]
adj = [[] for _ in range(N)]          # point -> lines (remaining)
for l, pts in enumerate(lines):
    for p in pts:
        adj[p].append(l)

def perfect_matching(adj):
    INF = 1 << 30
    mp = [-1] * N; ml = [-1] * N
    for p in range(N):
        random.shuffle(adj[p])
    def bfs():
        dist = [INF] * N; dq = deque()
        for p in range(N):
            if mp[p] < 0: dist[p] = 0; dq.append(p)
        found = False
        while dq:
            p = dq.popleft()
            for l in adj[p]:
                p2 = ml[l]
                if p2 < 0: found = True
                elif dist[p2] == INF: dist[p2] = dist[p] + 1; dq.append(p2)
        return found, dist
    while True:
        found, dist = bfs()
        if not found: break
        def dfs(p):
            for l in adj[p]:
                p2 = ml[l]
                if p2 < 0 or (dist[p2] == dist[p] + 1 and dfs(p2)):
                    mp[p] = l; ml[l] = p; return True
            dist[p] = 1 << 30; return False
        sys.setrecursionlimit(100000)
        for p in range(N):
            if mp[p] < 0: dfs(p)
    assert all(x >= 0 for x in mp)
    return mp

sigs = []
for t in range(j):
    mp = perfect_matching(adj)
    sigs.append(mp)
    for p in range(N):
        adj[p].remove(mp[p])
# flag index of (p, l): position of p in lines[l]
with open(out, 'w') as f:
    f.write(f"{q} {j} {max(m,1)} 7 -1\ncyc {max(m,1)}\n")
    for t in range(j):
        f.write(' '.join(map(str, sigs[t])) + '\n')
    for t in range(j):
        f.write(' '.join(str(random.randrange(m) if m > 0 else 0) for _ in range(N)) + '\n')
    f.write(' '.join(str(random.randrange(m) if m > 0 else 0) for _ in range(N * Q1)) + '\n')
print('wrote', out)
