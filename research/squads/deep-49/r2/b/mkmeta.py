"""Write the multiplication table (hx format) and automorphism generators of Z_m x|_r Z_k.
Element (a,j) -> a + m*j; (a,j)(b,l) = (a + r^j b, j + l).  Automorphisms (verified): (a,j) -> (u a + c S_j, j)
with S_j = 1 + r + ... + r^(j-1), for u a unit mod m and c in Z_m (kept only if a homomorphism), plus
(a,j) -> (a, t j) style maps when valid.  Usage: mkmeta.py m k r OUTPREFIX"""
import sys, numpy as np
m,k,r=map(int,sys.argv[1:4]); out=sys.argv[4]; N=m*k
rp=[pow(r,j,m) for j in range(k)]
a=np.arange(N)%m; j=np.arange(N)//m
MT=((a[:,None]+np.array(rp)[j][:,None]*a[None,:])%m + m*((j[:,None]+j[None,:])%k)).astype(np.uint16)
assert pow(r,k,m)==1%m
with open(out+'.tab','wb') as f:
    np.array([N],dtype=np.int32).tofile(f); MT.tofile(f)
Sj=[0]*(k+1)
for t in range(1,k+1): Sj[t]=(Sj[t-1]+rp[t-1])%m
def ishom(p):
    rng=np.random.default_rng(1)
    for _ in range(300):
        x,y=rng.integers(0,N,2)
        if p[MT[x,y]]!=MT[p[x],p[y]]: return False
    return bool(np.all(np.sort(p)==np.arange(N)))
gens=[]
from math import gcd
cands=[]
for u in range(1,m):
    if gcd(u,m)==1: cands.append((u,0,1))
for c in range(m): cands.append((1,c,1))
# j-scaling t with (0,1)->(0,t): needs r^t = r, i.e. maps j -> t j with a twist; try images of generators directly
for t in range(1,k):
    if gcd(t,k)==1: cands.append((1,0,t))
def perm(u,c,t):
    # image of (a,j): generator x=(1,0) -> (u,0); y=(0,1) -> (c,t).  (a,j) = x^a y^j  -> (u a, 0)*(c,t)^j
    # (c,t)^j = (c*(1 + r^t + r^2t + ...), t j)
    p=np.zeros(N,dtype=np.int64)
    pw=[0]*(k+1)
    rt=pow(r,t,m); acc=0; cur=1
    for jj in range(k):
        pw[jj]=acc; acc=(acc+c*cur)%m; cur=cur*rt%m
    for jj in range(k):
        for aa in range(m):
            p[aa+m*jj]=((u*aa+pw[jj])%m) + m*((t*jj)%k)
    return p
def closure(gs, mod):
    S={1%mod}; fr=[1%mod]
    while fr:
        x=fr.pop(); 
        for g in gs:
            y=x*g%mod
            if y not in S: S.add(y); fr.append(y)
    return S
U=[u for (u,c,t) in cands if t==1 and c==0 and ishom(perm(u,0,1))]
Ug=[]; cl={1%m}
for u in U:
    if u not in cl: Ug.append(u); cl=closure(Ug,m)
C=[c for c in range(1,m) if ishom(perm(1,c,1))]
Cg=[min(C)] if C else []
T=[t for t in range(2,k) if gcd(t,k)==1 and ishom(perm(1,0,t))]
Tg=[]; clt={1%k}
for t in T:
    if t not in clt: Tg.append(t); clt=closure(Tg,k)
uniq=[perm(u,0,1) for u in Ug]+[perm(1,c,1) for c in Cg]+[perm(1,0,t) for t in Tg]
print('units in aut',len(U),'gens',Ug,'c',len(C),Cg,'t',T[:10],Tg)
gens=U
with open(out+'.aut','w') as f:
    f.write(f"{len(uniq)}\n")
    for p in uniq: f.write(" ".join(map(str,p.tolist()))+"\n")
print(N,len(gens),"aut generators kept",len(uniq))
