"""Random hub graph for NU units: line-side hub 2i ~ point-side hub 2k+1 links, every hub with exactly d links
(union of d random perfect matchings, no repeated links), retried until every two hubs of the same side are within distance 6
inside the hub graph alone. Output in the uhcheck EXTRAS format (NS = 0).
Usage: python3 randhub.py NU d SEED > extras"""
import sys, random, collections
NU, d, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
rng = random.Random(seed)
def attempt():
    """union of d random perfect matchings between the two sides, no repeated links"""
    E = set()
    for r in range(d):
        for _ in range(200):
            perm = list(range(NU)); rng.shuffle(perm)
            if all((a, perm[a]) not in E for a in range(NU)): break
        else:
            return None
        for a in range(NU): E.add((a, perm[a]))
    return E
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
