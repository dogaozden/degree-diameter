#!/usr/bin/env python3
"""c10: q-dependent, non-liftable Delta = 7 (type 1+3+3) families in PSL(2,q), m = 1.

S = {I} u O(X) u O(Y),  O(Z) = {Z, w Z w^-1, w^2 Z w^-2},  w = [[0,-1],[1,-1]] (order 3, so w^-1 = w^2).
Usage: gen_c10.py q m variant      prints lines "a b c d z" (z = 0), one per element of S.
Exit 2 if the variant is not applicable at q (no square root / no cube root of unity) or S is degenerate
(orbit sizes or PSL-classes not all distinct).  g = least primitive root mod q.
Variants (entries are functions of q, g, and where needed sqrt(-1), sqrt(2), sqrt(3), zeta = g^((q-1)/3)):
  1  X=[[g,1],[0,g^-1]]            Y=[[1,g],[g,1+g^2]]                 (card example)
  2  X=[[1,g],[0,1]][[1,0],[g^2,1]] Y=[[1,1],[0,1]][[1,0],[g,1]]      (products of unipotents)
  3  X=[[g,1],[0,g^-1]]            Y=[[g^-1,0],[1,g]]
  4  X=[[1,g],[0,1]]               Y=[[1,0],[g,1]]                    (unipotent lower/upper)
  5  X=[[g,1],[0,g^-1]]            Y=[[2,1],[1,1]]                    (q-free Y)
  6  X=[[2,1],[1,1]]               Y=[[1,2],[2,5]]                    (q-free, integer matrices)
  7  X=[[z,g],[0,z^2]], z=zeta     Y=[[1,g],[g,1+g^2]]                (needs q = 1 mod 3)
  8  X=[[i,1],[0,-i]], i^2=-1      Y=[[1,g],[g,1+g^2]]                (needs q = 1 mod 4)
  9  X=[[i,1],[0,-i]]              Y=[[g,1],[0,g^-1]]                 (needs q = 1 mod 4)
 10  X=[[1,s],[s,3]], s^2=2        Y=[[1/2,1],[g,2+2g]]               (needs 2 a square)
 11  X=[[2,s],[s,2]], s^2=3        Y=[[1,g],[g,1+g^2]]                (needs 3 a square)
 12  X=[[g,1],[0,g^-1]]            Y=[[1/2,g],[g,2(1+g^2)]]           (1/2 entry)
 13  X=[[g,1],[0,g^-1]]            Y=[[g,0],[1,g^-1]]
 14  X=[[g^2,1],[0,g^-2]]          Y=[[1,g],[g,1+g^2]]
 15  X=[[g,0],[0,g^-1]]            Y=[[1,1],[0,1]]                    (split torus + unipotent)
 16  X=[[1,1],[0,1]]               Y=[[1,0],[1,1]]                    (q-free, standard SL2(Z) generators)
"""
import sys

def least_prim_root(q):
    primes = [p for p in range(2, q) if (q - 1) % p == 0 and all(p % d for d in range(2, int(p ** .5) + 1))]
    for g in range(2, q):
        if all(pow(g, (q - 1) // p, q) != 1 for p in primes):
            return g

class NA(Exception):
    pass

def sqrt_mod(x, q):
    for r in range(q):
        if r * r % q == x % q:
            return r
    raise NA('no square root of %d mod %d' % (x, q))

def mul(X, Y, q):
    a, b, c, d = X; e, f, h, i = Y
    return ((a * e + b * h) % q, (a * f + b * i) % q, (c * e + d * h) % q, (c * f + d * i) % q)

def variant(v, q):
    g = least_prim_root(q); inv = lambda x: pow(x % q, q - 2, q)
    gi, g2, g2i = inv(g), g * g % q, inv(g * g)
    M = lambda *e: tuple(x % q for x in e)
    Yg = M(1, g, g, 1 + g2)                       # the card's Y
    if v == 1:  return M(g, 1, 0, gi), Yg
    if v == 2:  return mul(M(1, g, 0, 1), M(1, 0, g2, 1), q), mul(M(1, 1, 0, 1), M(1, 0, g, 1), q)
    if v == 3:  return M(g, 1, 0, gi), M(gi, 0, 1, g)
    if v == 4:  return M(1, g, 0, 1), M(1, 0, g, 1)
    if v == 5:  return M(g, 1, 0, gi), M(2, 1, 1, 1)
    if v == 6:  return M(2, 1, 1, 1), M(1, 2, 2, 5)
    if v == 7:
        if (q - 1) % 3: raise NA('q != 1 mod 3')
        z = pow(g, (q - 1) // 3, q)
        return M(z, g, 0, z * z), Yg
    if v in (8, 9):
        if (q - 1) % 4: raise NA('q != 1 mod 4')
        i = sqrt_mod(-1, q)
        return M(i, 1, 0, -i), (Yg if v == 8 else M(g, 1, 0, gi))
    if v == 10:
        s = sqrt_mod(2, q)
        return M(1, s, s, 3), M(inv(2), 1, g, 2 + 2 * g)
    if v == 11:
        s = sqrt_mod(3, q)
        return M(2, s, s, 2), Yg
    if v == 12: return M(g, 1, 0, gi), M(inv(2), g, g, 2 * (1 + g2))
    if v == 13: return M(g, 1, 0, gi), M(g, 0, 1, gi)
    if v == 14: return M(g2, 1, 0, g2i), Yg
    if v == 15: return M(g, 0, 0, gi), M(1, 1, 0, 1)
    if v == 16: return M(1, 1, 0, 1), M(1, 0, 1, 1)
    raise NA('unknown variant %d' % v)

def main():
    q, m, v = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    try:
        X, Y = variant(v, q)
    except NA as e:
        print('NA', e, file=sys.stderr); sys.exit(2)
    w = (0, q - 1, 1, q - 1); w2 = mul(w, w, q)          # w^-1 = w^2 since w^3 = I
    assert mul(w2, w, q) == (1, 0, 0, 1)
    I = (1, 0, 0, 1)
    conj = lambda Z: mul(mul(w, Z, q), w2, q)
    def orbit(Z):
        O = [Z]; O.append(conj(Z)); O.append(conj(O[1]))
        return O
    S = [I] + orbit(X) + orbit(Y)
    for Z in S:
        a, b, c, d = Z
        assert (a * d - b * c) % q == 1, 'not in SL'
    def key(Z):                                             # PSL class: Z ~ -Z
        a, b, c, d = Z; lead = a if a else b
        return Z if lead <= (q - 1) // 2 else tuple((-t) % q for t in Z)
    if len({key(Z) for Z in S}) != 7:
        print('degenerate S', file=sys.stderr); sys.exit(2)
    for Z in S:
        print(*Z, 0)

if __name__ == '__main__':
    main()
