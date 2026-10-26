import sys, collections
from math import gcd
def mk(m,k,r,t):
    rp=[pow(r,e,m) for e in range(k)]
    def mul(g,h):
        a,j=g%m,g//m; b,l=h%m,h//m
        s=j+l
        if s<k: J,ex=s,0
        else: J,ex=s-k,t
        return (a+rp[j]*b+ex*rp[J])%m + m*J
    return mul
def order(mul,g,e,lim):
    p=g;o=1
    while p!=e and o<=lim:
        p=mul(p,g);o+=1
    return o
lines=open('cands.txt').read().split('\n')[1:]
seen={}
kept=[]
for ln in lines:
    if not ln.strip(): continue
    m,k,r,t=map(int,ln.split())
    N=m*k; mul=mk(m,k,r,t); e=0
    # split iff some a^c x has order k
    units=[u for u in range(1,k) if gcd(u,k)==1] or [1]
    split=k>1 and any(order(mul,c+m*u,e,k+1)==k for c in range(m) for u in units)
    if split: continue
    # invariant: order histogram (computed on all elements, cheap enough for N~1100)
    hist=collections.Counter(order(mul,g,e,N) for g in range(N))
    inv=(N,tuple(sorted(hist.items())))
    if inv in seen: continue
    seen[inv]=(m,k,r,t)
    kept.append((m,k,r,t,dict(hist)))
print(len(lines),'candidates; kept',len(kept),'nonsplit distinct-invariant')
for x in kept: print(*x[:4], x[4])
