# Predicted coverage wall (Poisson model on H-marginal of non-backtracking walks, length 11) for H-variants:
# orbit H-parts (u^i a, j0), i=0..4 with u = r^UE; fixed letter f H-part (0, jf). Scaling a is a symmetry, so a=1.
import math
from collections import defaultdict
P=191
r=None
for t in range(2,P):
    x=pow(t,38,P)
    if x!=1: r=x; break
def hmul(x,y):
    return ((x[0]+pow(r,x[1],P)*y[0])%P,(x[1]+y[1])%5)
def hinv(x):
    a,j=x
    return ((-pow(r,(5-j)%5,P)*a)%P,(5-j)%5)
def walk_vals(S,L=11):
    Sinv=[hinv(s) for s in S]
    dist={((0,0),-1):1}
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
    return [W.get((a,j),0) for a in range(P) for j in range(5)]
NSL=32736
def pred(vals): return sum(NSL*math.exp(-w/NSL) for w in vals)
res=[]
for e in (1,2):
    u=pow(r,e,P)
    for j0 in range(1,5):
        orb=[((pow(u,i,P))%P, j0) for i in range(5)]
        for jf in range(0,5):
            S=[(0,0),(0,jf)]+orb
            v=walk_vals(S)
            res.append((round(pred(v),1), e, j0, jf, min(v)/NSL))
res.sort()
for x in res[:8]: print("pred_holes=%s u=r^%d j0=%d jf=%d minW/N_SL=%.2f" % x)
print("worst:", res[-1])
# baseline: uniform (random-S) model value
print("uniform baseline:", round(NSL*955*math.exp(-423263232/(NSL*955)),1))
