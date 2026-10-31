import sys
from collections import deque
def load(fn):
    with open(fn) as f:
        toks = f.read().split()
    n = int(toks[0]); e = [(int(toks[i]), int(toks[i+1])) for i in range(1, len(toks), 2)]
    adj = [[] for _ in range(n)]
    for a, b in e:
        adj[a].append(b); adj[b].append(a)
    return n, adj
def bfs(adj, s):
    d = [-1]*len(adj); d[s] = 0; q = deque([s])
    while q:
        x = q.popleft()
        for y in adj[x]:
            if d[y] < 0: d[y] = d[x]+1; q.append(y)
    return d
if __name__ == "__main__":
    n, adj = load(sys.argv[1])
    col = bfs(adj, 0)
    col = [c % 2 for c in col]
    far = []
    for s in range(n):
        d = bfs(adj, s)
        for t in range(s+1, n):
            if d[t] < 0 or d[t] > 7: far.append((s, t, d[t]))
    same = sum(1 for s,t,_ in far if col[s]==col[t])
    print("far", len(far), "same-side", same, "opp-side", len(far)-same)
    from collections import Counter
    print("dist hist", Counter(x[2] for x in far))
    vc = Counter()
    for s,t,_ in far: vc[s]+=1; vc[t]+=1
    print("vertices in far pairs", len(vc), "max per vertex", max(vc.values()))
    print("far vertices", sorted(vc.items())[:60])
