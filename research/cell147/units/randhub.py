"""Random hub graph for NU units: line-side hub 2i ~ point-side hub 2k+1 links, every hub with exactly d links
(circulant with d distinct random shifts, no repeated links), retried until every two hubs of the same side are within distance 6
inside the hub graph alone. Output in the uhcheck EXTRAS format (NS = 0).
Usage: python3 randhub.py NU d SEED > extras"""
import sys, random, collections
NU, d, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
rng = random.Random(seed)
def attempt():
    """circulant: line-side hub a ~ point-side hub (a + s) mod NU for d distinct random shifts s (no repeated links)"""
    if d > NU: return None
    S = rng.sample(range(NU), d)
    return set((a, (a + s) % NU) for a in range(NU) for s in S)
def ecc_ok(E):
    adj = collections.defaultdict(list)
    for a, b in E: adj[('L', a)].append(('P', b)); adj[('P', b)].append(('L', a))
    worst = 0
    for side in 'LP':
        for s in range(NU):
            src = (side, s); dist = {src: 0}; dq = collections.deque([src])
            while dq:
                x = dq.popleft()
                for y in adj[x]:
                    if y not in dist: dist[y] = dist[x] + 1; dq.append(y)
            same = [dist.get((side, j), 99) for j in range(NU)]
            worst = max(worst, max(same))
            if worst > 6: return worst
    return worst
for tries in range(1, 500):
    E = attempt()
    if E is None: continue
    w = ecc_ok(E)
    if w <= 6: break
print(0)
for a, b in sorted(E): print(2 * a, 2 * b + 1)
print('randhub: NU=%d d=%d tries=%d same-side diameter %d' % (NU, d, tries, w), file=sys.stderr)
