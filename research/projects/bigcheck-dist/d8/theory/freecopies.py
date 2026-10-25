"""Search permutation pairs (pi1, pi2) on n copies such that the always-available routes cover every copy.
Point->line moves (left to right): [],U1,U2,D1,D2,UsUt (4),UsDt (s!=t),DsUt (s!=t); line->point: reversed words.
U_t = apply pi_t, D_t = apply pi_t^{-1}."""
import random, sys, itertools
def words():
    PL = [(), ('U1',), ('U2',), ('D1',), ('D2',)]
    PL += [('U%d' % s, 'U%d' % t) for s in (1, 2) for t in (1, 2)]
    PL += [('U%d' % s, 'D%d' % t) for s in (1, 2) for t in (1, 2) if s != t]
    PL += [('D%d' % s, 'U%d' % t) for s in (1, 2) for t in (1, 2) if s != t]
    inv = {'U1': 'D1', 'U2': 'D2', 'D1': 'U1', 'D2': 'U2'}
    LP = [tuple(inv[m] for m in reversed(w)) for w in PL]
    return PL, LP
PL, LP = words()
def missing(p1, p2, n):
    i1 = [0] * n; i2 = [0] * n
    for x in range(n): i1[p1[x]] = x; i2[p2[x]] = x
    mv = {'U1': p1, 'U2': p2, 'D1': i1, 'D2': i2}
    miss = 0
    for W in (PL, LP):
        for u in range(n):
            seen = set()
            for w in W:
                v = u
                for m in w: v = mv[m][v]
                seen.add(v)
            miss += n - len(seen)
    return miss
def search(n, iters, seed):
    rng = random.Random(seed)
    p1 = list(range(n)); p2 = list(range(n)); rng.shuffle(p1); rng.shuffle(p2)
    cur = missing(p1, p2, n); best = cur
    T = 1.0
    for it in range(iters):
        P = p1 if rng.random() < 0.5 else p2
        i, j = rng.sample(range(n), 2)
        P[i], P[j] = P[j], P[i]
        c = missing(p1, p2, n)
        if c <= cur or rng.random() < pow(2.718, (cur - c) / T):
            cur = c
            if c < best:
                best = c
            if c == 0:
                return p1, p2
        else:
            P[i], P[j] = P[j], P[i]
        T = max(0.05, T * 0.9995)
    return None, best
for n in map(int, sys.argv[1:]):
    found = None
    for seed in range(40):
        r = search(n, 20000, seed)
        if r[0] is not None:
            found = r; break
    print(n, 'FOUND' if found else 'none', found if found else '')
