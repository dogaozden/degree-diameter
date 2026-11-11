import numpy as np, sys, random
N=2523
with open('g2523.bin','rb') as f:
    n=np.frombuffer(f.read(4),dtype=np.int32)[0]; T=np.frombuffer(f.read(),dtype=np.uint16).reshape(n,n)
inv=np.array([int(np.where(T[g]==0)[0][0]) for g in range(N)])
def gen(gens):
    H={0}; frontier=[0]
    while frontier:
        nf=[]
        for h in frontier:
            for g in gens:
                x=int(T[h,g])
                if x not in H: H.add(x); nf.append(x)
        frontier=nf
    return len(H)
random.seed(5)
from collections import Counter
c=Counter()
for _ in range(30):
    S=[0]+random.sample(range(1,N),3)
    T_=[int(T[inv[s],t]) for s in S for t in S]
    c[gen(T_)]+=1
print("order of <S^-1 S> over 30 random S:", dict(c))
# element-order and j-structure: which elements have order 3
print("orders sample:", [sum(1 for _ in [0]) ])
exec(open('chk.py').read().split('for _ in range(3)')[0].replace("N=int(sys.argv[1]); fn=sys.argv[2]","N=2523;fn='g2523.bin'"))
random.seed(7); cnt=0; costs=[]
while cnt<12:
    S=[0]+random.sample(range(1,N),3)
    T_=[int(T[inv[s],t]) for s in S for t in S]
    if gen(T_)!=N: continue
    cnt+=1; costs.append(cost(S))
print("connected random S costs:", costs)
