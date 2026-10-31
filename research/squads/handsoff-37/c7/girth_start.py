# girth_start.py N SEED STEPS OUT: random cubic bipartite graph on N vertices (A = 0..m-1), then 2-switches that
# reduce the number of 4-cycles (pairs of same-side vertices with >= 2 common neighbours, counted as C(common,2)).
import random, sys
from itertools import combinations
n = int(sys.argv[1]); seed = int(sys.argv[2]); steps = int(sys.argv[3]); out = sys.argv[4]
random.seed(seed); m = n // 2
def rand_graph():
    while True:
        E = set(); ok = True
        for _ in range(3):
            p = list(range(m)); random.shuffle(p)
            for i in range(m):
                e = (i, m + p[i])
                if e in E: ok = False
                E.add(e)
            if not ok: break
        if ok and len(E) == 3 * m: return E
def c4(E):
    nbA = [[] for _ in range(m)]
    for a, b in E: nbA[a].append(b)
    cnt = {}
    tot = 0
    nbB = [[] for _ in range(m)]
    for a, b in E: nbB[b - m].append(a)
    for b in range(m):
        for a1, a2 in combinations(sorted(nbB[b]), 2):
            cnt[(a1, a2)] = cnt.get((a1, a2), 0) + 1
    for v in cnt.values():
        if v >= 2: tot += v * (v - 1) // 2
    return tot
E = rand_graph(); El = sorted(E); cur = c4(E)
print("start 4-cycle count", cur)
for s in range(steps):
    if cur == 0: break
    e1, e2 = random.sample(sorted(E), 2)
    a1, b1 = e1; a2, b2 = e2
    if a1 == a2 or b1 == b2: continue
    if (a1, b2) in E or (a2, b1) in E: continue
    E2 = set(E); E2.discard(e1); E2.discard(e2); E2.add((a1, b2)); E2.add((a2, b1))
    c = c4(E2)
    if c <= cur:
        E, cur = E2, c
print("final 4-cycle count", cur, "edges", len(E))
with open(out, "w") as f:
    f.write(f"{n}\n")
    for a, b in sorted(E): f.write(f"{a} {b}\n")
