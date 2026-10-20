"""Subgroups of the stabiliser of (W(3,q), regular spread S) in the K^2 model of w3k.py, as point permutations.

Spec: generators joined by '+'. Each generator:
  u:t        unipotent (a,b) -> (a, b + t a), t an element of K given as its index in GF(q^2) (u:1 means t=1)
  uF         all u:t for t in F (order q)
  uK         all u:t for t in K (order q^2)
  ul:k       u:t with t = gamma^k
  t:k        torus diag(gamma^k, gamma^-k)
  tf:k       diag(gamma^k, 1) composed with nothing: det = gamma^k must be in F (k multiple of q+1)
  ns:k       k-th power of a Singer-type element of order q^2+1 (multiplication by lambda in E, N(lambda) in F)
  sw         (a,b) -> (b,-a)
  fq         (a,b) -> (a^q, b^q)
  fp:e       (a,b) -> (a^(p^e), b^(p^e))
"""
import random

from w3k import W3


def perm_order(perm):
    n = len(perm)
    seen = [False] * n
    from math import gcd
    o = 1
    for s in range(n):
        if seen[s]:
            continue
        c, x = 0, s
        while not seen[x]:
            seen[x] = True
            x = perm[x]
            c += 1
        o = o * c // gcd(o, c)
    return o


def compose(p1, p2):
    """first p1 then p2"""
    return [p2[p1[i]] for i in range(len(p1))]


def power(perm, k):
    r = list(range(len(perm)))
    b = perm
    while k:
        if k & 1:
            r = compose(r, b)
        b = compose(b, b)
        k >>= 1
    return r


_singer_cache = {}


def singer(W):
    """A permutation of order q^2+1 from the non-split torus with det in F*."""
    if W.q in _singer_cache:
        return _singer_cache[W.q]
    q = W.q
    Q = q * q
    # a nonsquare h of K: gamma itself (gamma generates K*, odd log)
    h = int(W.exp[1])
    Fs = set(W.F[1:])
    rng = random.Random(1)
    while True:
        al, be = rng.randrange(Q), rng.randrange(1, Q)
        nrm = W.add[W.mul[al, al], W.neg[W.mul[h, W.mul[be, be]]]]
        if int(nrm) not in Fs:
            continue
        g = (al, int(W.mul[be, h]), be, al)
        p = W.mat_perm(g)
        if perm_order(p) == q * q + 1:
            _singer_cache[q] = p
            return p


def gens(W, spec):
    q = W.q
    out = []
    for part in spec.split('+'):
        if part == 'uF':
            out += [W.mat_perm((1, 0, t, 1)) for t in W.F[1:2]]  # F is generated additively by 1 when q = p
            if W.K.k // 2 > 1 or q != W.K.p:
                out += [W.mat_perm((1, 0, t, 1)) for t in W.F[1:]]
        elif part == 'uK':
            out += [W.mat_perm((1, 0, t, 1)) for t in range(1, q * q)]
        elif part.startswith('ul:'):
            k = int(part[3:])
            out.append(W.mat_perm((1, 0, int(W.exp[k % (q * q - 1)]), 1)))
        elif part.startswith('u:'):
            out.append(W.mat_perm((1, 0, int(part[2:]), 1)))
        elif part.startswith('t:'):
            k = int(part[2:])
            out.append(W.mat_perm((int(W.exp[k % (q * q - 1)]), 0, 0, int(W.exp[(-k) % (q * q - 1)]))))
        elif part.startswith('tf:'):
            k = int(part[3:])
            assert k % (q + 1) == 0
            out.append(W.mat_perm((int(W.exp[k % (q * q - 1)]), 0, 0, 1)))
        elif part.startswith('ns:'):
            out.append(power(singer(W), int(part[3:])))
        elif part == 'sw':
            out.append(W.mat_perm((0, 1, int(W.neg[1]), 0)))
        elif part == 'fq':
            out.append(W.frob_perm(W.K.k // 2))
        elif part.startswith('fp:'):
            out.append(W.frob_perm(int(part[3:])))
        else:
            raise ValueError(part)
    return out


if __name__ == '__main__':
    import sys
    from w3k import orbits
    q = int(sys.argv[1])
    W = W3(q)
    for spec in sys.argv[2:]:
        g = gens(W, spec)
        orbs, _ = orbits(len(W.pts), g)
        # check: each generator maps t.i. lines to t.i. lines and spread to spread
        lines = set(W.lines)
        sp = set(W.spread)
        for p in g:
            assert all(tuple(sorted(p[x] for x in L)) in lines for L in W.lines)
            assert all(tuple(sorted(p[x] for x in L)) in sp for L in W.spread)
        sizes = {}
        for o in orbs:
            sizes[len(o)] = sizes.get(len(o), 0) + 1
        print(spec, 'orders', [perm_order(p) for p in g][:5], 'orbits', len(orbs), sizes)
