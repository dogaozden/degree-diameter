# candidate groups for (6,12) orbit structures; N = group order, need 2N > 9,366,240 (N > 4,683,120)
import math
W = 6*(5**10+5**8+5**6+5**4+5**2+1)
def isprime(n):
    return n>1 and all(n%d for d in range(2,int(n**0.5)+1))
def ordmul(r,n):
    if math.gcd(r,n)!=1: return None
    k=1; x=r%n
    while x!=1 and k<10000: x=x*r%n; k+=1
    return k
def has_order(n,k):  # exists unit of order exactly k mod n (or k==1)
    if k==1 or n==1: return True
    for r in range(2,n):
        if math.gcd(r,n)==1 and ordmul(r,n)==k: return True
    return False
def psl(p): return p*(p*p-1)//2
def sl(p): return p*(p*p-1)
lo, hi = 4683121, 5000000
out=[]
# (ii) PSL(2,p) x Z_n with order-5 conjugation (needs p = +-1 mod 5); n with unit of order 5 or n=1
for p in range(5,400):
    if not isprime(p): continue
    for n in range(1,400):
        N=psl(p)*n
        if lo<=N<=hi and (p%5 in (1,4)) and (n==1 or has_order(n,5)):
            out.append(("ii k=5 PSL",p,n,N))
# (iii) PSL(2,p) x Z_n with order-3 conjugation (any p>3), n with unit of order 3 or n=1
for p in range(5,400):
    if not isprime(p): continue
    for n in range(1,400):
        N=psl(p)*n
        if lo<=N<=hi and (n==1 or has_order(n,3)):
            out.append(("iii k=3 PSL",p,n,N))
# (i) SL(2,32) x Z_n with field automorphism of order 5 on GF(32) (n with unit of order 5)
for n in range(1,400):
    N=32736*n
    if lo<=N<=hi and (n==1 or has_order(n,5)): out.append(("i k=5 SL(2,32) field",32,n,N))
for n in range(1,400):
    N=16368*n
    if lo<=N<=hi and (n==1 or has_order(n,5)): out.append(("i' k=5 PSL(2,32) field",32,n,N))
for t,p,n,N in sorted(out,key=lambda x:(x[0],x[3])):
    mu=N*math.exp(-W/N)
    print(f"{t:28s} q={p:4d} n={n:4d} N={N:9d} 2N={2*N:10d} mu={mu:6.2f}")
