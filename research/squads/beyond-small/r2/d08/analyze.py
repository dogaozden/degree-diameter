import numpy as np, collections, sys, pickle
H=16896
E=np.array(open('../../data/d16D5_n33792.edges').read().split(),dtype=np.int64)
n=int(E[0]); e=E[1:].reshape(-1,2)
u=np.minimum(e[:,0],e[:,1]); v=np.maximum(e[:,0],e[:,1])-H
adjA=np.zeros((H,16),np.int64); adjB=np.zeros((H,16),np.int64)
o=np.argsort(u,kind='stable'); adjA[:]=v[o].reshape(H,16)
o=np.argsort(v,kind='stable'); adjB[:]=u[o].reshape(H,16)
d2=adjA[adjB].reshape(H,256)          # B vertex -> B vertices at distance <=2 (with repeats), includes itself
cands=[list(map(int,l.split())) for l in open(sys.argv[1]) if l.strip()]
nc=len(cands); C=np.array([c[:16] for c in cands])
comp=np.zeros((nc,nc),bool)
for i in range(nc):
    m=np.zeros(H,bool); m[d2[C[i]].ravel()]=True
    meet=m[C].any(1)
    nm=np.zeros(H,np.int32); nm[C[i]]=1
    ov=nm[C].sum(1)
    comp[i]=meet&(ov==0)
np.fill_diagonal(comp,False)
deg=comp.sum(1)/(nc-1)
print('candidates',nc,'density',round(comp.sum()/(nc*(nc-1)),4))
print('degree quantiles',np.quantile(deg,[0,.05,.25,.5,.75,.95,1]).round(3))
def lines(c):
    return [(c[k]>>8,(c[k]&255)^(c[k+1]&255)) for k in range(0,len(c)-3,4)]
ncv=[];ndir=[]
for c in cands:
    L=lines(c); ncv.append(len(set(a for a,b in L))); ndir.append(len(set(b for a,b in L)))
ncv=np.array(ncv); ndir=np.array(ndir)
for k in range(1,5):
    m=ncv==k
    if m.sum(): print('distinct cvs',k,'count',m.sum(),'mean deg',deg[m].mean().round(4))
for k in range(1,5):
    m=ndir==k
    if m.sum(): print('distinct dirs',k,'count',m.sum(),'mean deg',deg[m].mean().round(4))
np.save('comp.npy',comp)
pickle.dump(cands,open('cands.pkl','wb'))
