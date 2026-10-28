#!/usr/bin/env python3
"""Card c4: alpha-closed Delta=7 set S in PSL(2,q) x Z_m, alpha(x,z) = (w x w^-1, r z), w=[[0,-1],[1,-1]] (w^3=I).
S = {(I,0)} u orbit(X,t) u orbit(Y,u), orbit(X,t) = {(X,t),(wXw^-1, r t),(w^2 X w^-2, r^2 t)}.
Usage: gen_c4.py q m X Y u [rchoice]
  X, Y: "a,b,c,d" integer matrices (det 1), reduced mod q.  t is fixed to 1 (WLOG: z -> t^-1 z is an automorphism commuting with alpha).
  u: integer (reduced mod m), or 'r' / 'r2' meaning u = r or r^2.
  rchoice: 'r' (smallest element of order 3 mod m, default) or 'R' (the other one).
For m=1 every z is 0 and the output is the m=1 integer family.
Prints 7 lines "a b c d z"."""
import sys

def mul(X, Y, q):
    a, b, c, d = X; e, g, h, i = Y
    return ((a*e+b*h) % q, (a*g+b*i) % q, (c*e+d*h) % q, (c*g+d*i) % q)

def order3_roots(m):
    if m == 1:
        return 0, 0
    rs = [r for r in range(2, m) if (r*r + r + 1) % m == 0]
    return (rs[0], rs[1]) if len(rs) == 2 else (rs[0], rs[0])

def gens(q, m, X, Y, u, rchoice='r'):
    r0, r1 = order3_roots(m)
    r = r0 if rchoice == 'r' else r1
    r2 = r * r % m if m > 1 else 0
    w = (0, q-1, 1, q-1); wi = (q-1, 1, q-1, 0)   # w^-1 = w^2
    def conj(M): return mul(mul(w, M, q), wi, q)
    def orbit(M, t):
        M0 = tuple(x % q for x in M)
        M1 = conj(M0); M2 = conj(M1)
        return [(M0, t % m), (M1, r*t % m), (M2, r2*t % m)]
    S = [((1, 0, 0, 1), 0)] + orbit(X, 1 % m if m > 1 else 0)
    if u == 'r': uu = r
    elif u == 'r2': uu = r2
    else: uu = int(u) % m if m > 1 else 0
    S += orbit(Y, uu)
    return S

def main():
    q, m = int(sys.argv[1]), int(sys.argv[2])
    X = tuple(map(int, sys.argv[3].split(',')))
    Y = tuple(map(int, sys.argv[4].split(',')))
    u = sys.argv[5]
    rc = sys.argv[6] if len(sys.argv) > 6 else 'r'
    for (a, b, c, d), z in gens(q, m, X, Y, u if u in ('r', 'r2') else u, rc):
        print(a, b, c, d, z)
if __name__ == '__main__':
    main()
