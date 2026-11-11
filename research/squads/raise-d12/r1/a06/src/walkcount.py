import numpy as np
L=open('/home/user/degree-diameter/research/squads/raise-d12/r1/a06/base.txt').read().split('\n')
V,E=map(int,L[0].split())
ed=[tuple(map(int,L[1+i].split())) for i in range(E)]
D=[]
for a,b in ed: D.append((a,b)); D.append((b,a))
D=np.array(D); M=len(D)            # directed edges
rev=np.arange(M)^1                  # reverse index
idx={ (int(a),int(b)):i for i,(a,b) in enumerate(D)}
# successors of directed edge e=(a,b): (b,c) with c != a
succ=[[] for _ in range(M)]
into=[[] for _ in range(V)]; outof=[[] for _ in range(V)]
for i,(a,b) in enumerate(D): outof[a].append(i); into[b].append(i)
for i,(a,b) in enumerate(D):
    for j in outof[b]:
        if D[j][1]!=a: succ[i].append(j)
# F[e,u] = number of NB walks from u of length k ending with directed edge e
F=np.zeros((M,V),dtype=np.float64)
for e,(a,b) in enumerate(D): F[e,a]=1.0
Wsum=np.zeros((V,V))
Wk={}
for k in range(1,13):
    Wk[k]=np.zeros((V,V))
    for v in range(V):
        Wk[k][:,v]=F[into[v],:].sum(axis=0)
    Wsum+=Wk[k]
    G=np.zeros_like(F)
    for i in range(M):
        if succ[i]:
            G[succ[i],:]+=F[i,:]
    F=G
np.save('/home/user/degree-diameter/research/squads/raise-d12/r1/a06/src/Wsum.npy',Wsum)
# diagnostics: NB walks length<=12 per (u,v), by parity class
same=np.arange(V)
pts=np.arange(364)
for name,(A,B) in {'pt-pt':(pts,pts),'pt-line':(pts,np.arange(364,728))}.items():
    x=Wsum[np.ix_(A,B)]
    print(name,'min',x.min(),'median',np.median(x),'max',x.max(), 'mean', x.mean())
print('k=12 total per source', Wk[12][0].sum(), 'k=6 to opposite', Wk[6][0].max())
for m in [85,90,97,100,105]:
    p=np.exp(-Wsum*np.log(1-1/m))  # approx (1-1/m)^N
    est=m*p.sum()
    print('m',m,'expected uncovered (independent model) ~', round(est,3))
