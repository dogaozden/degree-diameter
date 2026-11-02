# independent check: metacyclic group Z_m x|_r Z_k, Haar graph, BFS over the full bipartite graph (no tricks)
import sys, random
from collections import deque
m, k, r, D = 731, 48, 7, 12
def mul(a, b):
    ax, ay = a
    bx, by = b
    return ((ax + pow(r, ay, m) * bx) % m, (ay + by) % k)
G = [(x, y) for x in range(m) for y in range(k)]
e = (0, 0)
def inv(a):
    # brute inverse via search on the small group is too slow; use formula
    x, y = a
    yi = (-y) % k
    return ((-(pow(r, yi, m)) * x) % m, yi)
assert all(mul(a, inv(a)) == e for a in G[:2000])
def cost(S):
    # B nodes ('B', g); A nodes ('A', g); edges (g,A)-(s g,B)
    dist = {('A', e): 0}
    q = deque([('A', e)])
    while q:
        side, g = q.popleft()
        d = dist[(side, g)]
        if d >= 11:
            continue
        if side == 'A':
            nbrs = [('B', mul(s, g)) for s in S]
        else:
            nbrs = [('A', mul(inv(s), g)) for s in S]
        for nb in nbrs:
            if nb not in dist:
                dist[nb] = d + 1
                q.append(nb)
    return sum(1 for h in G if dist.get(('B', h), 99) > 11)
if __name__ == '__main__':
    random.seed(int(sys.argv[1]))
    for t in range(int(sys.argv[2])):
        S = random.sample(G[1:], 4)
        print(t, S, cost(S), flush=True)
