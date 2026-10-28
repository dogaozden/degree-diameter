"""local search for a large independent set (pairwise non-collinear) in W(5) / ovoid-type sets, for card c7"""
import sys, random, json, time
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
import numpy as np
from gqlib import W
Wg = W(5)
N = Wg.np
adj = [set(np.nonzero(Wg.col[p])[0].tolist()) for p in range(N)]
def search(target, seed, secs=200):
    rng = random.Random(seed)
    S = set(); conf = [0] * N   # conf[v] = number of S-neighbours
    best = []
    t0 = time.time(); it = 0
    tabu = {}
    while time.time() - t0 < secs:
        it += 1
        free = [v for v in range(N) if v not in S and conf[v] == 0]
        if free:
            v = rng.choice(free)
        else:
            # swap move: add v with conf 1, remove its unique S-neighbour
            cands = [v for v in range(N) if v not in S and conf[v] == 1 and tabu.get(v, 0) < it]
            if not cands:
                cands = [v for v in range(N) if v not in S and tabu.get(v, 0) < it]
            v = rng.choice(cands)
            for u in adj[v]:
                if u in S:
                    S.remove(u); tabu[u] = it + 7
                    for w in adj[u]: conf[w] -= 1
        S.add(v)
        for w in adj[v]: conf[w] += 1
        if len(S) > len(best):
            best = sorted(S)
            if len(best) >= target:
                break
    return best
if __name__ == '__main__':
    target = int(sys.argv[1]); seed = int(sys.argv[2]); secs = float(sys.argv[3])
    best = search(target, seed, secs)
    print('size', len(best))
    json.dump(best, open('/home/user/degree-diameter/research/squads/gqd5-r1/c7/P_ls_%d.json' % seed, 'w'))
