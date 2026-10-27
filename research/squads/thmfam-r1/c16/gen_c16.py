#!/usr/bin/env python3
"""c16 wildcard generators. Each prints generator lines "a b c d z" mod q (det 1 mod q, z = 0).
Modes (all take q as the LAST argument; family_score substitutes {q}):
  conic f X1 [X2 ...] q   Cayley-transform (conic / SO(3) model) family. X = "x,y,z" is the trace-zero matrix
                          [[x,y],[z,-x]], n = x^2+yz, C(X) = ((1+n)I - 2X)/(1-n) in SL(2,Q) (det 1, small height).
                          Each X gives the alpha-orbit {C(X), C(wXw^-1), C(w^2Xw^-2)}, w = [[0,-1],[1,-1]].
                          f = number of fixed letters added: 1 -> I, 2 -> I and C(X0) with X0=[[1,-2],[2,-1]] (= w^2 mod q).
  kloos a1,a2,... q       S = {T(a)}, T(a) = [[a,1],[-1,0]] (Kloosterman-type, det 1, no symmetry).
  cont a:b,c:d,... q      S = {T(a)T(b)} continuant words of length 2 (det 1, no symmetry).
  cayno X1 ... q          S = {C(X)} unsymmetric Cayley set (no orbit closure), for the symmetry ablation.
"""
import sys

def inv(a, q):
    return pow(a % q, q - 2, q)

def mm(X, Y, q):
    a, b, c, d = X; e, f, g, h = Y
    return ((a*e + b*g) % q, (a*f + b*h) % q, (c*e + d*g) % q, (c*f + d*h) % q)

def cayley(x, y, z, q):
    n = x*x + y*z
    if (1 - n) % q == 0:
        raise SystemExit('degenerate X (1-n = 0 mod q)')
    u = inv(1 - n, q)
    return (((1 + n - 2*x) * u) % q, (-2*y * u) % q, (-2*z * u) % q, ((1 + n + 2*x) * u) % q)

def conj_orbit_triples(x, y, z):
    # w = [[0,-1],[1,-1]], w^-1 = w^2 = [[-1,1],[-1,0]]; integer conjugation on trace-zero X
    X = (x, y, z)
    out = [X]
    def conjW(T):
        a, b, c = T
        M = [[a, b], [c, -a]]
        w = [[0, -1], [1, -1]]; wi = [[-1, 1], [-1, 0]]
        def mul(A, B):
            return [[sum(A[i][k]*B[k][j] for k in range(2)) for j in range(2)] for i in range(2)]
        R = mul(mul(w, M), wi)
        assert R[0][0] + R[1][1] == 0
        return (R[0][0], R[0][1], R[1][0])
    out.append(conjW(out[-1])); out.append(conjW(out[-1]))
    return out

def main():
    mode = sys.argv[1]; q = int(sys.argv[-1]); args = sys.argv[2:-1]
    mats = []
    if mode == 'conic':
        f = int(args[0]); xs = args[1:]
        if f >= 1: mats.append((1, 0, 0, 1))
        if f >= 2: mats.append(cayley(1, -2, 2, q))
        for s in xs:
            x, y, z = map(int, s.split(','))
            for T in conj_orbit_triples(x, y, z):
                mats.append(cayley(*T, q))
    elif mode == 'cayno':
        for s in args:
            x, y, z = map(int, s.split(','))
            mats.append(cayley(x, y, z, q))
    elif mode == 'kloos':
        for a in map(int, args[0].split(',')):
            mats.append((a % q, 1, q - 1, 0))
    elif mode == 'cont':
        for pr in args[0].split(','):
            a, b = map(int, pr.split(':'))
            Ta = (a % q, 1, q - 1, 0); Tb = (b % q, 1, q - 1, 0)
            mats.append(mm(Ta, Tb, q))
    else:
        raise SystemExit('unknown mode')
    if len(set(mats)) != len(mats):
        pass  # haar_ecc reports repeats itself
    for M in mats:
        print(*M, 0)

if __name__ == '__main__':
    main()
