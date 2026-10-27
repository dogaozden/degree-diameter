# Independent check of Lemma 4.4 at q=7: |Perp(h)| vs bound for fixed-point-free collineations h (checked) of H(7).
import sys, random, numpy as np, time
sys.path.insert(0,'/home/user/degree-diameter/research/omega_repair')
from geo import Hex
from mktwist import rand_elem
H=Hex('/home/user/degree-diameter/research/omega_repair/hex_q7.txt'); q=7; n=H.n; F=H.F
P=H.P % q
# Gram matrix of polar form of X0X4+X1X5+X2X6-X3^2
G=np.zeros((7,7),dtype=np.int64)
for i,j in ((0,4),(1,5),(2,6)): G[i,j]=G[j,i]=1
G[3,3]=-2
def Qf(X): return (X[:,0]*X[:,4]+X[:,1]*X[:,5]+X[:,2]*X[:,6]-X[:,3]**2)%q
assert (Qf(P)==0).all()
def rank(M):
    M=M.copy()%q; r=0
    for c in range(M.shape[1]):
        piv=next((i for i in range(r,M.shape[0]) if M[i,c]),None)
        if piv is None: continue
        M[[r,piv]]=M[[piv,r]]; M[r]=(M[r]*pow(int(M[r,c]),q-2,q))%q
        for i in range(M.shape[0]):
            if i!=r and M[i,c]: M[i]=(M[i]-M[i,c]*M[r])%q
        r+=1
    return r
def inv(M): return F.inv(M%q)
univ=(q**5-1)/(q-1)+q**3.5+q**3+(q-2)*q**1.5
print("universal bound",univ)
rng=random.Random(int(sys.argv[1])); S=int(sys.argv[2])
t0=time.time(); seen=0; fpf=0; maxperp=0; maxd=0; mingap=1e9; dist={}
def test(h):
    global seen,fpf,maxperp,maxd,mingap
    pp,lp=H.perm(h)  # raises if not a collineation
    seen+=1
    if (pp==np.arange(n)).any(): return
    fpf+=1
    hP=(P@h.T)%q
    perp=int(((np.einsum('ij,jk,ik->i',P,G,hP))%q==0).sum())
    # sanity: same with permuted representatives
    perp2=int(((np.einsum('ij,jk,ik->i',P,G,P[pp]))%q==0).sum()); assert perp==perp2
    S_=(h+inv(h))%q
    d=[7-rank((S_-c*np.eye(7,dtype=np.int64))%q) for c in range(q)]
    assert sum(d)<=7
    b=(q**5-1)/(q-1)+sum(q**(1.5+x/2) for x in d)
    assert perp<=b+1e-9, (perp,b,d)
    maxperp=max(maxperp,perp); maxd=max(maxd,max(d)); mingap=min(mingap,b-perp)
    key=(tuple(sorted([x for x in d if x],reverse=True)),perp); dist[key]=dist.get(key,0)+1
for s in range(S):
    h=rand_elem(H,rng,rng.choice([3,6,12,20]))%q
    test(h)
    # powers
    hk=h.copy()
    for k in range(2,7):
        hk=F.mm(hk,h)%q
        if (hk==np.eye(7,dtype=np.int64)).all(): break
        if rng.random()<0.5: test(hk)
print(f"tested {seen} collineations, {fpf} fpf; max|Perp|={maxperp}; max d_c={maxd}; min(own bound-|Perp|)={mingap:.1f}; time {time.time()-t0:.0f}s")
for k,v in sorted(dist.items()): print(k,v)
