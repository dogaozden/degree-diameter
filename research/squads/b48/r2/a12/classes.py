import itertools, collections
K = 28
def canon(J):
    best = None
    for t in J:
        for s in (1, -1):
            c = tuple(sorted((s * (j - t)) % K for j in J))
            if best is None or c < best: best = c
    return best
def qdiam(J):
    # Haar graph H(Z_K, J): A_i ~ B_{i+j}; eccentricity max over both sides from A_0 and B_0
    worst = 0
    for side in (0, 1):
        dist = {(side, 0): 0}; q = collections.deque([(side, 0)])
        while q:
            s, i = q.popleft()
            if s == 0:
                nb = [(1, (i + j) % K) for j in J]
            else:
                nb = [(0, (i - j) % K) for j in J]
            for v in nb:
                if v not in dist:
                    dist[v] = dist[(s, i)] + 1; q.append(v)
        if len(dist) < 2 * K: return 99
        worst = max(worst, max(dist.values()))
    return worst
if __name__ == '__main__':
    reps = set(); allsets = 0
    for a, b, c in itertools.combinations(range(1, K), 3):
        allsets += 1
        J = (0, a, b, c)
        reps.add(canon(J))
    print('4-sets containing 0:', allsets, 'translation+sign classes:', len(reps))
    good = [r for r in sorted(reps) if qdiam(r) <= 8]
    print('quotient diam <= 8:', len(good))
    print('diam histogram', collections.Counter(qdiam(r) for r in reps))
    open('reps.txt', 'w').write('\n'.join(' '.join(map(str, r)) for r in good) + '\n')
