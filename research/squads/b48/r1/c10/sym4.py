# Card c10 (i): orbit sets S = {x, a x, a^2 x, a^3 x}, a = scaling (t,j) -> (u t, j) of order 4 on Z_m x|_r Z_k.
# Exhaustive over x. Haar graph H(G,S) scored by the lift tool (dipole4, eval mode). Normalised S contains e.
import sys, subprocess, os
from math import gcd
from gen import metas
T='/home/user/degree-diameter/research/squads/b48/tools'
LIFT=T+'/lift'; BASE=T+'/bases/dipole4.txt'
def ops(m,k,r):
    rp=[pow(r,j,m) for j in range(k)]
    rinv=[pow(rp[j],-1,m) if gcd(rp[j],m)==1 else None for j in range(k)]
    def mul(x,y):
        a,j=x%m if False else (x%m, x//m); b,l=(y%m, y//m)
        return ((a+rp[j]*b)%m) + m*((j+l)%k)
    def inv(x):
        a,j=(x%m, x//m)
        return ((-rinv[j]*a)%m) + m*((-j)%k)
    return mul,inv
def order4_units(m):
    return [u for u in range(2,m) if gcd(u,m)==1 and pow(u,4,m)==1 and pow(u,2,m)!=1]
def run_group(N,m,k,r,u,seconds_note=None):
    mul,inv=ops(m,k,r)
    def phi(x):
        t,j=x%m,x//m
        return ((u*t)%m)+m*j
    lines=[]; xs=[]
    for x in range(N):
        o=[x]; y=x
        for _ in range(3):
            y=phi(y); o.append(y)
        if len(set(o))<4: continue
        if min(o)!=x: continue          # one representative per orbit
        xi=inv(x)
        S=[mul(s,xi) for s in o]       # right-translate so the first entry is e
        assert S[0]==0
        lines.append("%d %d %d %d"%tuple(S)); xs.append(x)
    if not lines: return None
    p=subprocess.run(["timeout","120","nice","-n","10",LIFT,BASE,"meta:%d:%d:%d"%(m,k,r),"4","8","eval"],
                     input="\n".join(lines)+"\n",capture_output=True,text=True,env=dict(os.environ,THREADS="1"))
    vals=p.stdout.split()
    best=None
    for x,v in zip(xs,vals):
        if v=="invalid": continue
        c=int(v)
        if best is None or c<best[0]: best=(c,x)
    return best, len(lines)
if __name__=="__main__":
    lo,hi,maxg=int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3])
    G=metas(lo,hi)
    res=[]
    cnt=0
    for (N,m,k,r) in G:
        us=order4_units(m)
        if not us: continue
        u=us[0]
        out=run_group(N,m,k,r,u)
        cnt+=1
        if out is None: continue
        best,nl=out
        res.append((best[0],N,m,k,r,u,best[1],nl))
        if cnt>=maxg: break
    res.sort()
    for row in res[:25]: print("cost=%d N=%d meta %d %d %d u=%d x=%d nlines=%d"%(row[0],row[1],row[2],row[3],row[4],row[5],row[6],row[7]))
    print("groups run:",cnt,"best:",res[0] if res else None)
