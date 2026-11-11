# End-to-end sanity check at q=7: five random collineations g_i, every point t: exact |U C_i|, structure type,
# perpendicular pairs; compare with Bonferroni bound per type and with sum of |Perp(h)| over the 15 elements.
import sys, random, numpy as np, itertools, time
sys.path.insert(0,'/home/user/degree-diameter/research/omega_repair')
from geo import Hex
from mktwist import rand_elem
H=Hex('/home/user/degree-diameter/research/omega_repair/hex_q7.txt'); q=7; n=H.n; F=H.F
P=H.P%q
G=np.zeros((7,7),dtype=np.int64)
for i,j in ((0,4),(1,5),(2,6)): G[i,j]=G[j,i]=1
G[3,3]=-2
PG=(P@G)%q
t0=time.time()
W=(n+7)//8
R=np.zeros((n,W),dtype=np.uint8)
for s in range(0,n,2000):
    R[s:s+2000]=np.packbits(((PG[s:s+2000]@P.T)%q==0),axis=1)
print("perp matrix",time.time()-t0)
pc=lambda X: np.bitwise_count(X).sum(axis=-1)
rng=random.Random(int(sys.argv[1]))
gs=[];perms=[]
while len(gs)<5:
    g=rand_elem(H,rng,12)%q; pp,lp=H.perm(g); gs.append(g); perms.append(pp)
inv=lambda p: np.argsort(p)
hs=[(i,) for i in range(5)]+[(i,j) for i,j in itertools.combinations(range(5),2)]
def hperm(k):
    if len(k)==1: return perms[k[0]]
    i,j=k; return inv(perms[i])[perms[j]]   # g_i^-1 g_j
fpf=[not (hperm(k)==np.arange(n)).any() for k in hs]
perpcount=[int((((PG*P[hperm(k)]).sum(1))%q==0).sum()) for k in hs]
print("fpf:",fpf); print("|Perp|:",perpcount,"sum",sum(perpcount))
Y=np.stack(perms)  # Y[i,t]=g_i(t)
U=np.zeros(n,dtype=np.int64); npp=np.zeros(n,dtype=np.int64)
for s in range(0,n,1000):
    ts=np.arange(s,min(n,s+1000))
    acc=np.zeros((len(ts),W),dtype=np.uint8)
    for i in range(5): acc|=R[Y[i,ts]]
    U[ts]=pc(acc & ~R[ts])
print("max exact union over t:",U.max(),"min",U.min(),"(general-position Bonferroni bound 9285)")
# perpendicular pairs per t
six=np.vstack([np.arange(n)[None,:],Y])
cnt=np.zeros(n,dtype=np.int64)
for a,b in itertools.combinations(range(6),2):
    cnt+=((((PG[six[a]]*P[six[b]]).sum(1))%q)==0)
print("sum over t of perp pairs:",cnt.sum(),"(should equal sum |Perp| =",sum(perpcount),")")
print("hist of perp pairs per t:",np.bincount(cnt))
print("far (ignoring radius-2 balls): min q^5-U =",q**5-U.max(), " t with q^5-U-6860<=0:",int(((q**5-U-6860)<=0).sum()))
print("time",time.time()-t0)
