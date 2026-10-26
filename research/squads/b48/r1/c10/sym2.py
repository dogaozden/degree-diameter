# Card c10 (ii): S = {x, a x, y, a y} with a(t,j) = (-t, j) (order 2, fixes j-parts), groups meta m k r.
# Random (x,y) sample, then exhaustive y for the best x values. Scored by lift eval (dipole4).
import sys, random, subprocess, os
from math import gcd
from sym4 import ops, LIFT, BASE
def evalS(lines,m,k,r):
    p=subprocess.run(["timeout","120","nice","-n","10",LIFT,BASE,"meta:%d:%d:%d"%(m,k,r),"4","8","eval"],
                     input="\n".join(lines)+"\n",capture_output=True,text=True,env=dict(os.environ,THREADS="1"))
    return [None if v=="invalid" else int(v) for v in p.stdout.split()]
def run(N,m,k,r,samples,topx,seed=1):
    random.seed(seed)
    mul,inv=ops(m,k,r)
    a=lambda x: ((-(x%m))%m)+m*(x//m)
    def mk(x,y):
        ax=a(x); ay=a(y); xi=inv(x)
        S=[mul(s,xi) for s in (x,ax,y,ay)]
        return "%d %d %d %d"%tuple(S)
    good=[x for x in range(N) if a(x)!=x]
    pairs=[]
    while len(pairs)<samples:
        x=random.choice(good); y=random.randrange(N)
        if y in (x,a(x)) or a(y)==y: continue
        pairs.append((x,y))
    vals=evalS([mk(x,y) for x,y in pairs],m,k,r)
    rank=sorted([(v,x,y) for (x,y),v in zip(pairs,vals) if v is not None])
    best=rank[0]
    # exhaustive y for the best topx distinct x
    seenx=[]; 
    for v,x,y in rank:
        if x not in seenx: seenx.append(x)
        if len(seenx)>=topx: break
    lines=[]; keys=[]
    for x in seenx:
        for y in range(N):
            if y in (x,a(x)) or a(y)==y: continue
            lines.append(mk(x,y)); keys.append((x,y))
    vals2=evalS(lines,m,k,r)
    rank2=sorted([(v,x,y) for (x,y),v in zip(keys,vals2) if v is not None])
    return rank[0], rank2[0], len(pairs)+len(lines)
if __name__=="__main__":
    N,m,k,r=map(int,sys.argv[1:5]); samples=int(sys.argv[5]); topx=int(sys.argv[6])
    b1,b2,ne=run(N,m,k,r,samples,topx)
    print("RANDOM best cost=%d x=%d y=%d"%b1); print("EXHAUSTIVE-y best cost=%d x=%d y=%d"%b2); print("evals",ne)
