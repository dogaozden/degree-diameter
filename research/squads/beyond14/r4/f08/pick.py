import sys, math
def isp(x):
    if x < 2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if x % p == 0: return x == p
    dd, s = x-1, 0
    while dd % 2 == 0: dd//=2; s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        y = pow(a, dd, x)
        if y in (1, x-1): continue
        for _ in range(s-1):
            y = y*y % x
            if y == x-1: break
        else: return False
    return True
def primes_of(n):
    ps=[]; p=2
    while p*p<=n:
        if n%p==0:
            ps.append(p)
            while n%p==0: n//=p
        p+=1
    if n>1: ps.append(n)
    return ps
lo, hi, kmin, kmax = map(int, sys.argv[1:5])
out=[]
for k in range(kmin, kmax+1):
    m0 = lo // k
    for m in range(m0-(m0%2==0 and 0), hi//k + 2):
        if m*k < lo or m*k > hi: continue
        if (m-1) % k or not isp(m): continue
        # exact-order-k element r
        for g in range(2, m):
            r = pow(g, (m-1)//k, m)
            if all(pow(r, k//p, m) != 1 for p in primes_of(k)) and pow(r,k,m)==1:
                break
        out.append((m*k, m, k, r))
out.sort()
for N,m,k,r in out: print(N, m, k, r)
