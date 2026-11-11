import numpy as np, pickle, collections
nt=396
M=np.fromfile('ta.M',dtype=np.uint16).reshape(nt,nt).astype(int)
T=[tuple(map(int,l.split())) for l in open('ta.types')]
idx={t:i for i,t in enumerate(T)}
cands=pickle.load(open('cands.pkl','rb')); comp=np.load('comp.npy')
nc=len(cands)
def lt(c):
    out=[]
    for k in range(0,16,4):
        cv=c[k]>>8; d=(c[k]&255)^(c[k+1]&255)
        out.append(idx.get((cv,d),-1))
    return out
LT=[lt(c) for c in cands]
print('lines not in type set:', sum(1 for L in LT for x in L if x<0))
# for each pair, max M over 16 line-type pairs
miss=0; tot=0; stats=collections.Counter()
rng=np.random.default_rng(1)
for _ in range(20000):
    i,j=rng.integers(nc,size=2)
    if i==j: continue
    mx=max(M[a,b] for a in LT[i] for b in LT[j] if a>=0 and b>=0)
    s=sum(1 for a in LT[i] for b in LT[j] if a>=0 and b>=0 and M[a,b]==0)
    stats[(bool(comp[i,j]), 'maxM=4096' if mx==4096 else ('maxM>0' if mx>0 else 'all0'))]+=1
for k,v in sorted(stats.items()): print(k,v)
