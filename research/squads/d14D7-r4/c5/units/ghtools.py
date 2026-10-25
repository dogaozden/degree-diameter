"""Small helpers: load GH(q) incidence, BFS distances, read glift state files."""
import collections
def load_gh(fn):
    with open(fn) as f:
        P, q = map(int, f.readline().split())
        lines = [list(map(int, f.readline().split())) for _ in range(P)]
    adj = [[] for _ in range(2 * P)]
    for l, pts in enumerate(lines):
        for p in pts:
            adj[p].append(P + l); adj[P + l].append(p)
    return P, q, lines, adj
def bfs(adj, s):
    d = [-1] * len(adj); d[s] = 0; dq = collections.deque([s])
    while dq:
        x = dq.popleft()
        for y in adj[x]:
            if d[y] < 0: d[y] = d[x] + 1; dq.append(y)
    return d
def read_state(fn, P, q):
    with open(fn) as f:
        hdr = f.readline().split(); J = int(hdr[2]); m = int(hdr[3]); f.readline()
        sig = []; hv = []
        for p in range(P):
            a = list(map(int, f.readline().split())); sig.append(a[0::2]); hv.append(a[1::2])
        fv = [list(map(int, f.readline().split())) for _ in range(P)]
    return J, m, sig, hv, fv
