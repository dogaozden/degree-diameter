# indep_bits.py EDGES [D]: independent checker (no tools/ code). Bit-parallel reach sets:
# R_k(v) = bitset of vertices at distance <= k from v. Prints n, edges, min/max degree, bipartite,
# connected, exact diameter (or None if > 40), far pairs at distance > D (ordered and unordered).
import sys
def main():
    path = sys.argv[1]
    D = int(sys.argv[2]) if len(sys.argv) > 2 else 9
    with open(path) as f:
        toks = f.read().split()
    n = int(toks[0])
    adj = [[] for _ in range(n)]
    m = 0
    for i in range(1, len(toks) - 1, 2):
        u, v = int(toks[i]), int(toks[i + 1])
        if u == v or not (0 <= u < n and 0 <= v < n):
            print("BAD_EDGE", u, v); return
        adj[u].append(v); adj[v].append(u); m += 1
    degs = [len(a) for a in adj]
    # bipartite check by BFS 2-colouring
    col = [-1] * n; bip = True; comps = 0
    for s in range(n):
        if col[s] != -1: continue
        comps += 1; col[s] = 0; q = [s]
        for x in q:
            for y in adj[x]:
                if col[y] == -1:
                    col[y] = 1 - col[x]; q.append(y)
                elif col[y] == col[x]:
                    bip = False
    full = (1 << n) - 1
    R = [1 << v for v in range(n)]
    k = 0; diam = None; farD = None
    while True:
        if all(r == full for r in R):
            diam = k; break
        if k == D:
            farD = sum(n - bin(r).count("1") for r in R)
        if k > 40: break
        newR = []
        for v in range(n):
            r = R[v]
            for u in adj[v]:
                r |= R[u]
            newR.append(r)
        R = newR; k += 1
    if farD is None:
        farD = sum(n - bin(r).count("1") for r in R)
    print("n=%d edges=%d deg=%d-%d bipartite=%s components=%d diameter=%s far_D_ordered=%d far_D_unordered=%d"
          % (n, m, min(degs), max(degs), "yes" if bip else "no", comps, diam, farD, farD // 2))
main()
