# Diagnostic: is <S^-1 S> (the Haar-connectivity subgroup) all of PSL(2,p)?  S = {e} + conj-orbit of x (k=5) or 2 orbits (k=3)
import random, sys
p=int(sys.argv[1]); k=int(sys.argv[2]); trials=int(sys.argv[3]); random.seed(5)
def mul(a,b):
    A=(a[0]*b[0]+a[1]*b[2])%p; B=(a[0]*b[1]+a[1]*b[3])%p; C=(a[2]*b[0]+a[3]*b[2])%p; D=(a[2]*b[1]+a[3]*b[3])%p
    return (A,B,C,D)
def norm(a):  # PSL: identify a and -a
    a=tuple(x%p for x in a)
    neg=tuple((-x)%p for x in a)
    return min(a,neg)
def inv(a):  # det 1
    return (a[3]%p,(-a[1])%p,(-a[2])%p,a[0]%p)
def closure(gens):
    gens=[norm(g) for g in gens]
    seen={norm((1,0,0,1))}; frontier=[norm((1,0,0,1))]
    while frontier:
        nf=[]
        for h in frontier:
            for g in gens:
                y=norm(mul(h,g))
                if y not in seen: seen.add(y); nf.append(y)
        frontier=nf
    return len(seen)
def rnd_sl():
    while True:
        a,b,c=[random.randrange(p) for _ in range(3)]
        if a==0 and b==0: continue
        # find d with ad-bc=1
        if a%p==0: continue
        d=(1+b*c)*pow(a,-1,p)%p
        return (a,b,c,d)
def order(g):
    x=g; n=1
    while norm(x)!=norm((1,0,0,1)): x=mul(x,g); n+=1
    return n
# find element h of order k (conjugator) in SL(2,p)
def find_order(k):
    while True:
        g=rnd_sl()
        if order(g) in (k,2*k):
            x=g
            # reduce to order k in PSL
            y=(1,0,0,1)
            for _ in range(2*k):
                y=mul(y,g)
                if norm(y)==norm((1,0,0,1)): break
            # find element of exact PSL order k
            for t in range(1,2*k):
                z=(1,0,0,1)
                for _ in range(t): z=mul(z,g)
                # order in PSL
                if norm(z)!=norm((1,0,0,1)):
                    u=z; m=1
                    while norm(u)!=norm((1,0,0,1)): u=mul(u,z); m+=1
                    if m==k: return z
hit=0; sizes=[]
N=p*(p*p-1)//2
for _ in range(trials):
    h=find_order(k)
    if k==5: orbits=1
    else: orbits=2
    S=[]
    if k==5: S=[(1,0,0,1)]
    for o in range(orbits):
        x=rnd_sl(); cur=x
        for i in range(k):
            S.append(cur); cur=mul(mul(h,cur),inv(h))
    gens=[mul(inv(s),t) for s in S for t in S]  # all S^-1 S products as generators
    c=closure(gens)
    sizes.append(c)
    if c==N: hit+=1
print(f"p={p} k={k} PSL order={N}: connected(<S^-1 S>=G) in {hit}/{trials}; sizes {sorted(set(sizes))[:6]}")
