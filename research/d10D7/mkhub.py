"""Hub graphs for d7hex mode 3: "K m" then m lines "j k" (line-side hub j ~ point-side hub k).
   python3 mkhub.py pg r out           incidence graph of PG(2,r), r prime (K = r^2+r+1, degree r+1)
   python3 mkhub.py rnd K d seed out   random d-regular bipartite graph on K+K hubs, same-side distance <= 4 checked"""
import random, sys
from collections import deque

def pg(r):
    pts = []
    for a in range(r):
        for b in range(r):
            for c in range(r):
                v = (a, b, c); f = next((x for x in v if x), 0)
                if f == 1: pts.append(v)
    E = [(j, k) for j, P in enumerate(pts) for k, Q in enumerate(pts) if sum(x * y for x, y in zip(P, Q)) % r == 0]
    return len(pts), E

def rnd(K, d, seed):
    """union of d edge-disjoint random perfect matchings (each redrawn until disjoint from the previous ones)"""
    rng = random.Random(seed); E = set()
    for _ in range(d):
        while True:
            perm = list(range(K)); rng.shuffle(perm)
            if all((j, perm[j]) not in E for j in range(K)): break
        E.update((j, perm[j]) for j in range(K))
    return sorted(E)

def same_side_ecc(K, E):
    adj = [[] for _ in range(2 * K)]
    for j, k in E: adj[j].append(K + k); adj[K + k].append(j)
    worst = 0
    for s in range(2 * K):
        dist = [-1] * (2 * K); dist[s] = 0; dq = deque([s])
        while dq:
            v = dq.popleft()
            for w in adj[v]:
                if dist[w] < 0: dist[w] = dist[v] + 1; dq.append(w)
        side = range(0, K) if s < K else range(K, 2 * K)
        m = max(dist[t] if dist[t] >= 0 else 99 for t in side)
        worst = max(worst, m)
    return worst

if __name__ == "__main__":
    if sys.argv[1] == "pg":
        K, E = pg(int(sys.argv[2])); out = sys.argv[3]
    else:
        K, d, seed, out = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
        E = rnd(K, d, seed)
    print("K", K, "edges", len(E), "same-side ecc in hub graph", same_side_ecc(K, E))
    with open(out, "w") as f:
        f.write(f"{K} {len(E)}\n"); f.writelines(f"{j} {k}\n" for j, k in E)
