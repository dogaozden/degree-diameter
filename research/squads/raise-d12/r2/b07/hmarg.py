# H-marginal wall check for b07: count non-backtracking B-level walks of length 11 (odd length) per H-value.
# Predicted holes per H-fiber (fiber = SL(2,32), 32736 elements): 32736 * exp(-W_h/32736) under a Poisson model.
import math, sys
P=191
r=None
for t in range(2,P):
    x=pow(t,38,P)
    if x!=1: r=x; break
def hmul(x,y):
    a1,j1=x; a2,j2=y
    return ((a1+pow(r,j1,P)*a2)%P,(j1+j2)%5)
def hinv(x):
    a,j=x
    # (a,j)^-1 = (-r^{-j} a, -j)
    return ((-pow(r,(5-j)%5,P)*a)%P,(5-j)%5)
S=[(0,0),(0,0)]+[(int(a),int(j)) for a,j in [(183,4),(181,4),(83,4),(56,4),(70,4)]]
# S contains e and f (both H-part identity); treat as 7 letter indices
def walk_counts(S, L):
    Sinv=[hinv(s) for s in S]
    # state: dict (h,last) -> count ; step t odd uses S, even uses Sinv; non-backtracking: index differs from last
    from collections import defaultdict
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
    return W
L=int(sys.argv[1]) if len(sys.argv)>1 else 11
W=walk_counts(S,L)
tot=sum(W.values())
NSL=32736
vals=[W.get((a,j),0) for a in range(P) for j in range(5)]
pred=sum(NSL*math.exp(-w/NSL) for w in vals)
print("total walks len",L,":",tot,"  distinct H-values reached:",sum(1 for v in vals if v>0),"of 955")
print("min W_h =",min(vals),"  median W_h =",sorted(vals)[477],"  max W_h =",max(vals))
print("Poisson-model predicted holes (sum over H-fibers):", round(pred,1))
print("W_h/N_SL quantiles: min %.2f  10%% %.2f  median %.2f" % (min(vals)/NSL, sorted(vals)[95]/NSL, sorted(vals)[477]/NSL))
