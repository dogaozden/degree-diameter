"""Discrete logs in E = GF(q^4) = K[delta]/(delta^2 - gamma) for points of the K^2 model (a,b) <-> a + b delta."""
from w3k import W3

def elog_table(W):
    q = W.q; Q = q * q; K = W.K
    gam = int(W.exp[1])
    add, mul = W.add, W.mul
    def emul(x, y):
        a, b = x; c, d = y
        return (int(add[mul[a, c], mul[gam, mul[b, d]]]), int(add[mul[a, d], mul[b, c]]))
    order = Q * Q - 1
    # find primitive g: try candidates
    import itertools
    for cand in itertools.product(range(Q), range(1, Q)):
        x = (1, 0); seen = 0; ok = True
        # check order via powers of primes dividing order
        def epow(z, e):
            r = (1, 0)
            while e:
                if e & 1: r = emul(r, z)
                z = emul(z, z); e >>= 1
            return r
        ps = [p for p in range(2, order + 1) if order % p == 0 and all(p % r for r in range(2, int(p**0.5) + 1))]
        if all(epow(cand, order // p) != (1, 0) for p in ps):
            g = cand; break
    log = {}
    x = (1, 0)
    for i in range(order):
        log[x] = i
        x = emul(x, g)
    return log, g

if __name__ == '__main__':
    import json, sys
    d = json.load(open(sys.argv[1])); q = d['q']; W = W3(q)
    log, g = elog_table(W)
    N = (q**4 - 1) // (q - 1)
    M = d['M']
    idx = sorted(log[W.pts[p]] % (N // 2) for p in M)
    print('pair indices mod N/2 =', N // 2, ':', sorted(set(idx)))
    for mod in [q + 1, (q + 1) // 2, (q * q + 1) // 2, q * q + 1, 5, 10, 25, 40]:
        print(mod, sorted(set(i % mod for i in idx)))
