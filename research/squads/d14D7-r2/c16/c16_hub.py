"""c16_hub.py: hub graph for NU type-2 units, in the uhcheck EXTRAS format (NS = 0).
Replacement for ../cell147/units/randhub.py, which crashes when d is large relative to NU (its rejection sampling of
d disjoint perfect matchings without repeated links fails, leaving E = None). Here the hub graph is the circulant
bipartite graph: line-like hub a ~ point-like hub (a + s) mod NU for d distinct shifts s (simple, d-regular).
Shifts are retried until every two hubs of the same side are within distance 6 inside the hub graph alone.
Usage: python3 c16_hub.py NU d SEED > extras"""
import sys, random, collections
NU, d, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
rng = random.Random(seed)

def same_side_diameter(E):
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
            worst = max(worst, max(dist.get((side, j), 99) for j in range(NU)))
    return worst

best = None
for tries in range(1, 2001):
    shifts = sorted(rng.sample(range(NU), d))
    E = {(a, (a + s) % NU) for a in range(NU) for s in shifts}
    w = same_side_diameter(E)
    if best is None or w < best[0]:
        best = (w, E, shifts)
    if w <= 6:
        break
w, E, shifts = best
print(0)
for a, b in sorted(E):
    print(2 * a, 2 * b + 1)
print('c16_hub: NU=%d d=%d shifts=%s tries=%d same-side diameter %d' % (NU, d, shifts, tries, w), file=sys.stderr)
