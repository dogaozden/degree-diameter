#!/usr/bin/env python3
"""Enumerate/sample non-cyclic groups K x| Q for cay_mq.  A spec is a dict R,C,A,B,P1,P2 (+name).
Families:  F0  Z_m x| Z_n  (m any, r of order n)      [baseline, = old family]
           F1  Z_m x| (Z_a x Z_b)  faithful on cyclic kernel Z_m (m composite)
           F2d Z_p^2 x| (Z_a x Z_b)  diag matrices, faithful      (a,b | p-1)
           F2s Z_p^2 x| Z_a  Singer (irreducible) element of F_{p^2}^*, order a"""
import random, math
from functools import lru_cache
from math import gcd
def isprime(n):
    if n<2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n%p==0: return n==p
    d=n-1;s=0
    while d%2==0: d//=2;s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,n)
        if x in(1,n-1): continue
        for _ in range(s-1):
            x=x*x%n
            if x==n-1: break
        else: return False
    return True
def factorint(n):
    f={};p=2
    while p*p<=n:
        while n%p==0: f[p]=f.get(p,0)+1; n//=p
        p+=1 if p==2 else 2
    if n>1: f[n]=f.get(n,0)+1
    return f
def primerange(a,b):
    return [p for p in range(max(2,a),b) if isprime(p)]
@lru_cache(None)
def primitive_root(p):
    if p==2: return 1
    fs=list(factorint(p-1))
    g=2
    while True:
        if all(pow(g,(p-1)//q,p)!=1 for q in fs): return g
        g+=1
@lru_cache(None)
def fac(m): return factorint(m)
def carm(m):
    l=1
    for p,k in fac(m).items():
        if p==2: c=1 if k==1 else (2 if k==2 else 2**(k-2))
        else: c=(p-1)*p**(k-1)
        l=l*c//gcd(l,c)
    return l
def divisors(n):
    ds=[1]
    for p,k in factorint(n).items(): ds=[d*p**i for d in ds for i in range(k+1)]
    return sorted(ds)
def order_mod(r,m,lam=None):
    lam=lam or carm(m)
    o=lam
    for p in fac(lam):
        while o%p==0 and pow(r,o//p,m)==1: o//=p
    return o
def rand_unit_of_order_dividing(m,a,rng):
    lam=carm(m); g=gcd(a,lam)
    while True:
        x=rng.randrange(2,m)
        if gcd(x,m)==1: break
    return pow(x,lam//g,m)
def spec_cyc(m,a,b,r1,r2): return dict(R=1,C=m,A=a,B=b,P1=[r1,0,0,0],P2=[r2,0,0,0])
# --- F0 / F1
def sample_cyc(lo,hi,rng,b_choices=(1,),amin=3,tries=200):
    for _ in range(tries):
        b=rng.choice(b_choices)
        if b>1:
            a=rng.randint(max(2,b),max(b,int(1.5*(hi/ (1.0))**(1/3))))   # a>=b
        else:
            a=rng.randint(amin,int(2.4*hi**(1/3)))
        n=a*b; mlo=-(-lo//n); mhi=hi//n
        if mhi<mlo or mlo<5: continue
        m=rng.randint(mlo,mhi)
        if m%2==0 and b>1: pass
        lam=carm(m)
        if lam%a or (b>1 and lam%b): continue
        for _ in range(30):
            r1=rand_unit_of_order_dividing(m,a,rng); r2=rand_unit_of_order_dividing(m,b,rng) if b>1 else 1
            if order_mod(r1,m,lam)!=a: continue
            if b>1:
                if order_mod(r2,m,lam)!=b: continue
                S={pow(r1,i,m)*pow(r2,j,m)%m for i in range(a) for j in range(b)}
                if len(S)!=a*b: continue
            return spec_cyc(m,a,b,r1,r2)
    return None
# --- F2: Z_p^2
def mm(X,Y,p): return [(X[0]*Y[0]+X[1]*Y[2])%p,(X[0]*Y[1]+X[1]*Y[3])%p,(X[2]*Y[0]+X[3]*Y[2])%p,(X[2]*Y[1]+X[3]*Y[3])%p]
def mpow(X,e,p):
    r=[1,0,0,1]; b=list(X)
    while e:
        if e&1: r=mm(r,b,p)
        b=mm(b,b,p); e>>=1
    return r
def spec_2d(p,a,b,P1,P2): return dict(R=p,C=p,A=a,B=b,P1=P1,P2=P2)
def sample_2d_diag(p,a,b,rng,tries=60):
    g=primitive_root(p)
    if (p-1)%a or (p-1)%b: return None
    for _ in range(tries):
        l1=pow(g,rng.randrange(p-1)*((p-1)//a)%(p-1),p); u1=pow(g,rng.randrange(p-1)*((p-1)//a)%(p-1),p)
        l2=pow(g,rng.randrange(p-1)*((p-1)//b)%(p-1),p); u2=pow(g,rng.randrange(p-1)*((p-1)//b)%(p-1),p)
        P1=[l1,0,0,u1];P2=[l2,0,0,u2]
        S={(pow(l1,i,p)*pow(l2,j,p)%p,pow(u1,i,p)*pow(u2,j,p)%p) for i in range(a) for j in range(b)}
        if len(S)==a*b: return spec_2d(p,a,b,P1,P2)
    return None
def sample_2d_singer(p,a,rng,tries=60):
    # element z of F_{p^2}^* of order exactly a, not in F_p ; matrix of mult by z on basis (1,w), w^2=eps
    if (p*p-1)%a or a<=2: return None
    eps=next(e for e in range(2,p) if pow(e,(p-1)//2,p)==p-1) if p>2 else None
    if eps is None: return None
    def mul(x,y): return ((x[0]*y[0]+eps*x[1]*y[1])%p,(x[0]*y[1]+x[1]*y[0])%p)
    def pw(x,e):
        r=(1,0)
        while e:
            if e&1:r=mul(r,x)
            x=mul(x,x); e>>=1
        return r
    for _ in range(tries):
        x=(rng.randrange(p),rng.randrange(1,p))
        z=pw(x,(p*p-1)//a)
        if z[1]==0: continue
        # exact order a?
        ok=all(pw(z,a//q)!=(1,0) for q in factorint(a))
        if not ok or pw(z,a)!=(1,0): continue
        # mult by z: z*(1)=(z0,z1), z*w=(eps z1, z0): matrix columns
        M=[z[0],(eps*z[1])%p,z[1],z[0]]
        return spec_2d(p,a,1,M,[1,0,0,1])
    return None
def enum_2d(lo,hi,rng,fam,nmin=6):
    out=[]
    pmax=int((hi/nmin)**.5)+1
    for p in primerange(7,pmax+1):
        q=p*p; nlo=max(nmin,-(-lo//q)); nhi=hi//q
        if nhi<nlo: continue
        for n in range(nlo,nhi+1):
            if fam=='F2s':
                s=sample_2d_singer(p,n,rng)
                if s: out.append(s)
            elif fam=='F2d':
                for a in divisors(n):
                    b=n//a
                    if a<b or (p-1)%a or (p-1)%b: continue
                    s=sample_2d_diag(p,a,b,rng)
                    if s: out.append(s)
    return out
def order_of(s): return s['A']*s['B']*s['C']*(s['C'] if s['R']>1 else 1)
def args_of(s): return [s['R'],s['C'],s['A'],s['B']]+list(s['P1'])+list(s['P2'])
def name_of(s): return f"R{s['R']}C{s['C']}A{s['A']}B{s['B']}P1{'_'.join(map(str,s['P1']))}P2{'_'.join(map(str,s['P2']))}"
if __name__=='__main__':
    import sys
    lo,hi=int(sys.argv[1]),int(sys.argv[2]); rng=random.Random(1)
    for fam in ('F2s','F2d'):
        L=enum_2d(lo,hi,rng,fam); print(fam,len(L)); 
        for s in L[:5]: print(order_of(s),args_of(s))
    c=[sample_cyc(lo,hi,rng,(1,)) for _ in range(300)]; print('F0',sum(1 for x in c if x))
    c=[sample_cyc(lo,hi,rng,(2,3,4,5,6)) for _ in range(2000)]; c=[x for x in c if x]; print('F1',len(c)); 
    for s in c[:5]: print(order_of(s),args_of(s))

def sample_frob(lo,hi,rng,nmin=5,nmax=None,tries=400):
    """prime m, n | m-1, r of exact order n mod m (faithful Frobenius group); N=m*n in [lo,hi]"""
    from sympy import isprime
    nmax=nmax or int(3*hi**(1/3))
    for _ in range(tries):
        n=rng.randint(nmin,nmax); klo=-(-(-(-lo//n)-1)//n); khi=(hi//n-1)//n
        if khi<klo: continue
        k=rng.randint(klo,khi); m=1+n*k
        if m<lo//n or m>hi//n or not isprime(m): continue
        g=primitive_root(m); 
        while True:
            u=rng.randrange(1,n+1)
            if gcd(u,n)==1: break
        r=pow(g,(m-1)//n*u,m)
        return spec_cyc(m,n,1,r,1)
    return None
