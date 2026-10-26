# Card c10 (i) redo: order-4 automorphisms that move the Z_k part, so S = orbit of x is not in one coset.
# Family A: phi(t,j) = (u t, s j), u^4=1 mod m, s^4=1 mod k (units), r^(s-1)=1 mod m (homomorphism condition).
# Family B: conjugation by c with c^4=e (inner automorphism of order dividing 4).
# S = {x, phi x, phi^2 x, phi^3 x} (orbit of size 4), exhaustive over x, scored by lift eval (dipole4).
import sys, subprocess, os
from math import gcd
from gen import metas
from sym4 import ops, LIFT, BASE
def run_lines(N,m,k,r,phi_fn,mul,inv):
    lines=[]; xs=[]
    for x in range(N):
        o=[x]; y=x
        for _ in range(3):
            y=phi_fn(y); o.append(y)
        if len(set(o))<4 or min(o)!=x: continue
        if phi_fn(o[3])!=x: continue     # orbit closed after 4 steps
        xi=inv(x); S=[mul(s,xi) for s in o]
        lines.append("%d %d %d %d"%tuple(S)); xs.append(x)
    if not lines: return None
    p=subprocess.run(["timeout","120","nice","-n","10",LIFT,BASE,"meta:%d:%d:%d"%(m,k,r),"4","8","eval"],
                     input="\n".join(lines)+"\n",capture_output=True,text=True,env=dict(os.environ,THREADS="1"))
    best=None
    for x,v in zip(xs,p.stdout.split()):
        if v=="invalid": continue
        c=int(v)
        if best is None or c<best[0]: best=(c,x)
    return best, len(lines)
def families(N,m,k,r):
    out=[]
    for u in range(1,m):
        if gcd(u,m)!=1 or pow(u,4,m)!=1: continue
        for s in range(1,k):
            if gcd(s,k)!=1 or pow(s,4,k)!=1%k: continue
            if pow(r,(s-1)%k,m)!=1%m: continue
            if u==1 and s==1: continue
            out.append(("A",u,s))
    return out
if __name__=="__main__":
    lo,hi,maxg=int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3])
    G=metas(lo,hi); res=[]; ng=0; nfam=0
    for (N,m,k,r) in G:
        fams=families(N,m,k,r)
        if not fams: continue
        ng+=1
        mul,inv=ops(m,k,r)
        for (_,u,s) in fams:
            def phi(x,u=u,s=s):
                return ((u*(x%m))%m) + m*((s*(x//m))%k)
            out=run_lines(N,m,k,r,phi,mul,inv); nfam+=1
            if out is None: continue
            best,nl=out
            res.append((best[0],N,m,k,r,u,s,best[1],nl))
        if ng>=maxg: break
    res.sort()
    for row in res[:25]: print("cost=%d N=%d meta %d %d %d u=%d s=%d x=%d nlines=%d"%row)
    print("groups with family:",ng,"runs:",nfam,"best:",res[0] if res else None)
