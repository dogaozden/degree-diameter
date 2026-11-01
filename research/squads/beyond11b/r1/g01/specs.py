import sys, math
# enumerate Z_p^2 x| Z_k specs with M of exact order k (irreducible companion or scalar), deduped by Aut(Z_k) orbit
def primes(lo, hi):
    return [q for q in range(lo, hi+1) if all(q % r for r in range(2, int(q**0.5)+1))]
def mm(A, B, p):
    return ((A[0]*B[0]+A[1]*B[2])%p, (A[0]*B[1]+A[1]*B[3])%p, (A[2]*B[0]+A[3]*B[2])%p, (A[2]*B[1]+A[3]*B[3])%p)
def mpow(A, j, p):
    R = (1,0,0,1)
    for _ in range(j): R = mm(R, A, p)
    return R
def order(A, p, cap):
    R = A
    for o in range(1, cap+1):
        if R == (1,0,0,1): return o
        R = mm(R, A, p)
    return 0
def specs(D, lo, hi, kmin=3, kmax=200, odd=True):
    out = []
    for p in primes(3, 61):
        for k in range(kmin, kmax+1):
            if odd and k % 2 == 0: continue
            N = p*p*k
            if N < lo or N > hi: continue
            seen = set(); cands = []
            for t in range(p):
                for d in range(1, p):
                    M = (0, (-d) % p, 1, t)
                    if order(M, p, k) != k: continue
                    key = frozenset(mpow(M, j, p) for j in range(1, k) if math.gcd(j, k) == 1)
                    key = min(tuple(sorted(x)) for x in [key]) if False else tuple(sorted(key))
                    if key in seen: continue
                    seen.add(key); cands.append(M)
            for lam in range(2, p):
                M = (lam, 0, 0, lam)
                if order(M, p, k) != k: continue
                key = tuple(sorted(mpow(M, j, p) for j in range(1, k) if math.gcd(j, k) == 1))
                if key in seen: continue
                seen.add(key); cands.append(M)
            for M in cands:
                red = any(M[0]*0 == 0 and False for _ in [0])
                out.append((N, f"semi {p} {k} {M[0]} {M[1]} {M[2]} {M[3]}"))
    out.sort()
    return out
if __name__ == "__main__":
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    for N, s in specs(11, lo, hi):
        print(N, s)
