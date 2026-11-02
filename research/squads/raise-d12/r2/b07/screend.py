# Same H-marginal Poisson model for H = D_461 (order 922), beta(a,e) = (u a, e), u of order 5 mod 461.
# Element (a, e), e in {+1,-1}: (a,e)(b,d) = (a + e b, e d). Orbit of s=(1,+1): (u^i, +1). f: fixed (0,-1) or (0,+1) (order 2 / e).
import math
from collections import defaultdict
P=461
r=None
for t in range(2,P):
    x=pow(t,92,P)
    if x!=1: r=x; break
u=r
assert pow(u,5,P)==1 and u!=1
def hmul(x,y): return ((x[0]+x[1]*y[0])%P, x[1]*y[1])
def hinv(x): return ((-x[1]*x[0])%P, x[1])
def walk_vals(S,L=11):
    Sinv=[hinv(s) for s in S]
    dist={((0,1),-1):1}
    for t in range(1,L+1):
        nd=defaultdict(int)
        letters = S if t%2==1 else Sinv
        for (h,last),c in dist.items():
            for i,s in enumerate(letters):
                if last>=0 and i==last: continue
                nd[(hmul(s,h),i)] += c
        dist=nd
    W=defaultdict(int)
    for (h,last),c in dist.items(): W[h]+=c
    allH=[(a,e) for a in range(P) for e in (1,-1)]
    return [W.get(h,0) for h in allH]
NSL=32736; Hord=2*P
def pred(vals): return sum(NSL*math.exp(-w/NSL) for w in vals)
print("N =",NSL*Hord,"  uniform-model holes:",round(NSL*Hord*math.exp(-423263232/(NSL*Hord)),1) if False else "")
N=NSL*Hord
print("size-law mu (uniform) =", round(N*math.exp(-435357267/N),1))
if __name__=="__main__":
    print("N =",NSL*Hord)
    N=NSL*Hord
    print("size-law mu (uniform) =", round(N*math.exp(-435357267/N),1))
    for fe in [(0,-1),(0,1)]:
        orb=[(pow(u,i,P),1) for i in range(5)]
        S=[(0,1),fe]+orb
        v=walk_vals(S)
        print("f=%s pred_holes=%s minW/N=%.2f medW/N=%.2f" % (fe, round(pred(v),1), min(v)/NSL, sorted(v)[len(v)//2]/NSL))
