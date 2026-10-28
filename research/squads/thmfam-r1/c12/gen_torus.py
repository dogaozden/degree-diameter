#!/usr/bin/env python3
"""Card c12: S = {I} u union of T-conjugacy orbits in PSL(2,q), T = split or non-split torus.
Usage: gen_torus.py q kind norb seed [xmode]
  kind: split | nonsplit ; norb: number of orbits ; seed: RNG seed for generic x's
  xmode: 'rand' (default) generic random x per orbit; or 'fixed:a,b,c,d'
Prints generator lines 'a b c d 0' (PSL, det 1 mod q) for haar_ecc psl q 1."""
import sys, random

def mmul(X, Y, q):
    a, b, c, d = X; e, f, g, h = Y
    return ((a*e + b*g) % q, (a*f + b*h) % q, (c*e + d*g) % q, (c*f + d*h) % q)

def minv(X, q):
    a, b, c, d = X
    return (d % q, (-b) % q, (-c) % q, a % q)  # det 1

def canon(X, q):
    neg = tuple((-v) % q for v in X)
    return min(X, neg)

def psl_order(X, q, limit):
    I = (1, 0, 0, 1); negI = (q-1, 0, 0, q-1)
    P = X
    for k in range(1, limit+1):
        if canon(P, q) == canon(I, q):
            return k
        P = mmul(P, X, q)
    return None

def split_torus(q):
    # primitive root g
    for g in range(2, q):
        if all(pow(g, (q-1)//p, q) != 1 for p in set(factor(q-1))):
            break
    return (g, 0, 0, pow(g, q-2, q))

def factor(n):
    f = []; p = 2
    while p*p <= n:
        while n % p == 0:
            f.append(p); n //= p
        p += 1
    if n > 1: f.append(n)
    return f

def nonsplit_torus(q, rng):
    # companion matrix [[0,-1],[1,s]] of x^2 - s x + 1; need PSL order (q+1)/2
    target = (q+1)//2
    cands = list(range(q)); rng.shuffle(cands)
    for s in cands:
        M = (0, (q-1) % q, 1, s % q)
        if psl_order(M, q, target + 1) == target:
            return M
    raise SystemExit("no nonsplit torus element found")

def orbit(x, T, q, order):
    out = []
    Ti = (1, 0, 0, 1)
    for i in range(order):
        out.append(mmul(mmul(Ti, x, q), minv(Ti, q), q))
        Ti = mmul(Ti, T, q)
    return out

def main():
    q = int(sys.argv[1]); kind = sys.argv[2]; norb = int(sys.argv[3]); seed = int(sys.argv[4])
    xmode = sys.argv[5] if len(sys.argv) > 5 else 'rand'
    rng = random.Random(seed*1000003 + q)
    if kind == 'split':
        T = split_torus(q); tord = (q-1)//2
    else:
        T = nonsplit_torus(q, random.Random(q)); tord = (q+1)//2
    S = {canon((1, 0, 0, 1), q)}
    for o in range(norb):
        if xmode.startswith('fixed:'):
            x = tuple(int(v) % q for v in xmode[6:].split(','))
        else:
            while True:
                a = rng.randrange(1, q); b = rng.randrange(1, q); c = rng.randrange(1, q)
                d = ((1 + b*c) * pow(a, q-2, q)) % q
                x = (a, b, c, d)
                if (a*d - b*c) % q == 1: break
        for X in orbit(x, T, q, tord):
            S.add(canon(X, q))
    S = sorted(S)
    for X in S:
        print(*X, 0)
    sys.stderr.write(f"Delta={len(S)} q={q} kind={kind} norb={norb} tord={tord}\n")

if __name__ == '__main__':
    main()
