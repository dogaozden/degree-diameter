"""Count the 'Haar symmetries' of S in Z_p x|_r Z_k (Frobenius, Aut(G) = affine maps (a,j) -> (u a + c S_j, j)):
pairs (sigma, h) with sigma in Aut(G), h in G such that h sigma(T) h^-1 = T, T = S^-1 S (B side) -- a necessary
condition for sigma(S) to be a two-sided translate of S.  Also the same for T' = S S^-1."""
import sys, numpy as np
sys.path.insert(0,'.')
from meta import table, inv
p,k,r=map(int,sys.argv[1:4]); S=list(map(int,sys.argv[4:8])); N=p*k
MT=table(p,k,r); I=inv(MT)
rp=[pow(r,j,p) for j in range(k)]; Sj=[0]*k
for j in range(1,k): Sj[j]=(Sj[j-1]+rp[j-1])%p
a=np.arange(N)%p; jj=np.arange(N)//p
for side in ('S^-1S','SS^-1'):
    T=sorted({int(MT[I[s],t]) if side=='S^-1S' else int(MT[s,I[t]]) for s in S for t in S})
    Tset=np.zeros(N,bool); Tset[T]=True
    cnt=0; found=[]
    for u in range(1,p):
        for c in range(p):
            sig=((u*a+c*np.array(Sj)[jj])%p)+p*jj
            ST=sig[T]
            # conjugates h x h^-1 for all h: MT[h, MT[x, I[h]]]
            H=np.arange(N)
            conj=MT[H[:,None], MT[ST[None,:], I[H][:,None]]]   # N x 13
            ok=Tset[conj].all(axis=1)
            nh=int(ok.sum())
            if nh: cnt+=nh; found.append((u,c,nh))
    print(side,"(sigma,h) pairs with h sigma(T) h^-1 = T:",cnt,"sigmas:",[(u,c) for u,c,_ in found][:12])
