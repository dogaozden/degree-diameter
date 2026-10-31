"""Enumerate all automorphisms of a cubic bipartite graph (edge list, first number n) by backtracking.
usage: auts.py EDGES OUTFILE   -> writes one permutation per line (space separated images of 0..n-1)
and prints the order statistics of order-3 elements (fixed points per side)."""
import sys
sys.setrecursionlimit(10000)
from collections import deque

def read_graph(path):
    with open(path) as f:
        toks = f.read().split()
    n = int(toks[0])
    N = [[] for _ in range(n)]
    for i in range(1, len(toks), 2):
        a, b = int(toks[i]), int(toks[i + 1])
        N[a].append(b); N[b].append(a)
    return n, N

def automorphisms(n, N):
    Nset = [set(x) for x in N]
    # BFS order from vertex 0 with parent pointers
    order = [0]; parent = {0: None}; dq = deque([0])
    while dq:
        x = dq.popleft()
        for y in N[x]:
            if y not in parent:
                parent[y] = x; order.append(y); dq.append(y)
    assert len(order) == n
    # all-pairs distances (BFS from every vertex) for strong pruning
    D = []
    for s0 in range(n):
        d = [-1] * n; d[s0] = 0; q = deque([s0])
        while q:
            x = q.popleft()
            for y in N[x]:
                if d[y] < 0:
                    d[y] = d[x] + 1; q.append(y)
        D.append(d)
    sols = []
    f = [None] * n; inv = [None] * n
    def extend(k):
        if k == n:
            sols.append(list(f)); return
        v = order[k]
        if k == 0:
            cands = range(n)
        else:
            cands = N[f[parent[v]]]
        for c in cands:
            if inv[c] is not None:
                continue
            ok = True
            Dc = D[c]; Dv = D[v]
            for u in order[:k]:
                if Dv[u] != Dc[f[u]]:
                    ok = False; break
            if ok:
                f[v] = c; inv[c] = v
                extend(k + 1)
                f[v] = None; inv[c] = None
    extend(0)
    return sols

def cycle_type(p):
    n = len(p); seen = [False] * n; cyc = []
    for i in range(n):
        if not seen[i]:
            L = 0; j = i
            while not seen[j]:
                seen[j] = True; j = p[j]; L += 1
            cyc.append(L)
    return cyc

if __name__ == "__main__":
    n, N = read_graph(sys.argv[1])
    sols = automorphisms(n, N)
    print("automorphisms:", len(sols))
    with open(sys.argv[2], "w") as f:
        f.write("%d\n" % n)
        for p in sols:
            f.write(" ".join(map(str, p)) + "\n")
    from collections import Counter
    c = Counter()
    for p in sols:
        ct = cycle_type(p)
        c[(tuple(sorted(ct)))] += 1
    for k, v in sorted(c.items(), key=lambda kv: (-len(kv[0]), kv[0])):
        if all(x in (1, 2, 3) for x in k) or len(k) < 60:
            print("cycle type (fixed pts =", k.count(1), "):", v, "elements", "2-cycles", k.count(2), "3-cycles", k.count(3))
