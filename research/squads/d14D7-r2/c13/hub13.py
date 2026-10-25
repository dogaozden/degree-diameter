"""Hub graph for NU units (c13 variant of randhub.py). Line-side hub 2a ~ point-side hub 2b+1 for (a, b) in a
circulant bipartite graph: b = a + s (mod NU) for s in a random d-set S of shifts (simple, d-regular). Retried until
every two hubs of the same side are within distance 6 inside the hub graph alone (same test as randhub.py).
randhub.py fails for NU = 76, d = 10 (union of random perfect matchings runs out of 200 tries).
Usage: python3 hub13.py NU d SEED > extras   (EXTRAS format of uhcheck: first line NS = 0, then "a b" links)"""
import sys, random, collections
NU, d, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
rng = random.Random(seed)

def ecc(E):
    adj = collections.defaultdict(list)
    for a, b in E:
        adj[('L', a)].append(('P', b)); adj[('P', b)].append(('L', a))
    worst = 0
    for side in 'LP':
        for s in range(NU):
            src = (side, s); dist = {src: 0}; dq = collections.deque([src])
            while dq:
                x = dq.popleft()
                for y in adj[x]:
                    if y not in dist:
                        dist[y] = dist[x] + 1; dq.append(y)
            same = [dist.get((side, j), 99) for j in range(NU)]
            worst = max(worst, max(same))
    return worst

for tries in range(1, 2001):
    S = rng.sample(range(NU), d)
    E = set((a, (a + s) % NU) for s in S for a in range(NU))
    assert len(E) == NU * d
    w = ecc(E)
    if w <= 6:
        break
else:
    sys.exit("hub13: no hub graph found")
print(0)
for a, b in sorted(E): print(2 * a, 2 * b + 1)
print('hub13: NU=%d d=%d tries=%d same-side diameter %d' % (NU, d, tries, w), file=sys.stderr)
