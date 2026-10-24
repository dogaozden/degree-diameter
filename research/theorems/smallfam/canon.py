"""Canonical forms of Haar connection sets in G = Z_p x|_r Z_k (p prime, faithful action, k > 1).

H(G,S) is isomorphic to H(G, x S y) (x, y in G), to H(G, sigma(S)) (sigma in Aut G) and to H(G, S^-1) (swap sides).
Every normalized (e in S) image is sigma(S s^-1) or sigma((S s^-1)^-1) for some s in S and sigma in Aut G, since
s^-1 S = s^-1 (S s^-1) s is an inner image of S s^-1.  Aut G = AGL(1,p) acting by conjugation inside AGL(1,p):
(a, j) -> (u a + c (1 - r^j), j).  The canonical form is the lexicographically smallest sorted tuple over all images.
Distinct canonical forms = distinct S up to these isomorphisms (an upper bound on the number of graph classes).

Usage: python3 canon.py p k r SOLFILE      (SOL lines with element indices a*k + j)
"""
import sys


def canon(S, p, k, r):
    rp = [pow(r, j, p) for j in range(k)]

    def mul(x, y):
        return ((x[0] + rp[x[1]] * y[0]) % p, (x[1] + y[1]) % k)

    def inv(x):
        jj = (-x[1]) % k
        return ((-rp[jj] * x[0]) % p, jj)

    best = None
    for s in S:
        si = inv(s)
        T = [mul(t, si) for t in S]
        for TT in (T, [inv(t) for t in T]):
            for u in range(1, p):
                for c in range(p):
                    img = tuple(sorted(((u * a + c * (1 - rp[j])) % p, j) for (a, j) in TT))
                    if best is None or img < best:
                        best = img
    return best


if __name__ == '__main__':
    p, k, r, f = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
    sols = [[divmod(int(x), k) for x in l.split()[1:]] for l in open(f) if l.startswith('SOL')]
    classes = {}
    for S in sols:
        c = canon(S, p, k, r)
        classes.setdefault(c, []).append(S)
    print(f'{len(sols)} solutions, {len(classes)} classes up to translation, Aut(G) = AGL(1,{p}) and inversion')
    for c, L in classes.items():
        print('class', c, 'size', len(L))
