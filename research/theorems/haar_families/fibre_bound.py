"""Theorem C (fibre bound): for any Haar graph H(PGL(2,q) x K, S) whose projection to PGL(2,q) is the LPS set psi(S_p)
(p = 1 mod 4, q = 1 mod 4 prime, q > p), if the component of (e,A) has A-side PSL(2,q) x K and diameter <= D, then
|K| <= M(p,q,D) = sum over odd t, 1 <= t < 2P/q^2 (P = p^(D'/2), D' = largest even <= D) of
r'(t(2P - q^2 t)), r'(n) = #{(u,v,w) in Z^3 : u odd, v, w even, u^2+v^2+w^2 = n}.
Prints, for each (Delta, D), the largest possible order 2*|PSL(2,q)|*M over q, against the table and our records."""
import math, sys
from functools import lru_cache
def isprime(n): return n > 1 and all(n % d for d in range(2, int(n**.5)+1))
@lru_cache(None)
def rprime(n):
    c = 0; u = 1
    while u*u <= n:
        r = n - u*u; v = 0
        while v*v <= r:
            w2 = r - v*v; w = math.isqrt(w2)
            if w*w == w2 and v % 2 == 0 and w % 2 == 0:
                c += (2 if u else 1) * (2 if v else 1) * (2 if w else 1)
            v += 2
        u += 2
    return c
def M(p, q, D):
    Dp = D - (D % 2); P = p ** (Dp // 2); s = 0; t = 1
    while q*q*t < 2*P:
        s += rprime(t * (2*P - q*q*t)); t += 2
    return s
TABLE = {(6,8):29790,(6,9):117360,(6,10):452032,(14,8):14172480,(14,9):95087738,(14,10):1213477190,
         (18,8):None,(30,8):None}
if __name__ == '__main__':
    for p in [5, 13, 17, 29]:
        for D in [7, 8, 9, 10, 11, 12]:
            best = (0, None, None)
            for q in range(p+1, 20000):
                if not isprime(q) or q % 4 != 1: continue
                if q*q >= 2 * p ** ((D - D % 2)//2): break
                m = M(p, q, D); n = q*(q*q-1)*m
                if n > best[0]: best = (n, q, m)
            W = 2*sum(p**j for j in range(D))
            print(f"p={p} Delta={p+1} D={D}: max 2|PSL|*M = {best[0]:,} (q={best[1]}, M={best[2]}), {100*best[0]/W:.2f}% of Moore; table {TABLE.get((p+1,D))}")
