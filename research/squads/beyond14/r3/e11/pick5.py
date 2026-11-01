#!/usr/bin/env python3
"""pick5.py Nlo Nhi [kmin kmax]: Frobenius groups Z_m x|_r Z_k (m prime, k | m-1, r of exact order k mod m),
N = m*k in [Nlo, Nhi], k in [kmin,kmax]. Prints: N m k r  (sorted by N)."""
import sys, random
def isprime(n):
    if n < 2: return False
    for p in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if n % p == 0: return n == p
    d = n-1; s = 0
    while d % 2 == 0: d//=2; s+=1
    for a in [2,3,5,7,11,13,17]:
        x = pow(a,d,n)
        if x in (1,n-1): continue
        for _ in range(s-1):
            x = x*x % n
            if x == n-1: break
        else: return False
    return True
def primefactors(n):
    f=set(); d=2
    while d*d<=n:
        while n%d==0: f.add(d); n//=d
        d+=1
    if n>1: f.add(n)
    return f
def gen(m):
    # primitive root
    fs = primefactors(m-1)
    for g in range(2, m):
        if all(pow(g,(m-1)//q,m)!=1 for q in fs): return g
def exact_order_elt(m,k,rng):
    g = gen(m)
    base = pow(g,(m-1)//k,m)  # order exactly k
    return base
def main():
    Nlo,Nhi = int(sys.argv[1]), int(sys.argv[2])
    kmin,kmax = (int(sys.argv[3]),int(sys.argv[4])) if len(sys.argv)>4 else (30,100)
    out=[]
    for k in range(kmin,kmax+1):
        mlo = -(-Nlo//k); mhi = Nhi//k
        m = mlo + ((1-mlo)%k)  # m ≡ 1 mod k
        while m <= mhi:
            if isprime(m):
                r = exact_order_elt(m,k,None)
                out.append((m*k,m,k,r))
            m += k
    for N,m,k,r in sorted(out): print(N,m,k,r)
main()
