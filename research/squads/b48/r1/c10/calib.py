# calibration: random unconstrained 4-sets S (normalised, e first) on meta 55 20 2, same eval
import random, sys
from sym2 import evalS
from sym4 import ops
N,m,k,r=1100,55,20,2
random.seed(7); mul,inv=ops(m,k,r)
lines=[]
for _ in range(3000):
    S=random.sample(range(N),4)
    if 0 not in S: S=[0]+S[1:]
    x=S[random.randrange(4)]
    T=[mul(s,inv(x)) for s in S]
    T=[0]+[t for t in T if t!=0][:3]
    if len(set(T))<4: continue
    lines.append("%d %d %d %d"%tuple(T))
v=[c for c in evalS(lines,m,k,r) if c is not None]
v.sort(); print("random 4-sets: n=%d best=%d median=%d"%(len(v),v[0],v[len(v)//2]))
