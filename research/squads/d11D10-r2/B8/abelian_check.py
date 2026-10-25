# B8 sanity check of the abelian counting bound: in H(Z_N, S) with |S| = d, the number of B-vertices at
# odd distance <= D-1 from (0,A) is at most #{c in Z^d : sum c = 1, |c|_1 <= D-1}. Compare with a BFS.
import random, sys
sys.path.insert(0, '.')
from routes import count_c

def bfs_B_count(N, S, D):
    # BFS on H(Z_N,S): (g,0)~(g+s,1), (g,1)~(g-s,0). Returns number of B-vertices at odd distance <= D-1.
    dist = {}
    frontier = [(0, 0)]
    dist[(0, 0)] = 0
    for depth in range(1, D):
        nxt = []
        for (g, side) in frontier:
            if side == 0:
                for s in S:
                    v = ((g + s) % N, 1)
                    if v not in dist:
                        dist[v] = depth
                        nxt.append(v)
            else:
                for s in S:
                    v = ((g - s) % N, 0)
                    if v not in dist:
                        dist[v] = depth
                        nxt.append(v)
        frontier = nxt
    return sum(1 for (g, side), t in dist.items() if side == 1 and t % 2 == 1 and t <= D - 1)

random.seed(1)
for d, D in [(3, 6), (4, 6), (4, 8)]:
    N = 2_000_003
    S = random.sample(range(1, N), d)
    got = bfs_B_count(N, S, D)
    bound = count_c(d, D - 1)
    print("d=%d D=%d: BFS B-count = %d, abelian bound = %d, ok = %s" % (d, D, got, bound, got <= bound))
