"""Random cyclic subgroups of Sp(4,11); for each order d | elem order, exact max-weight union of compatible orbits (networkx B&B)."""
import sys,time,random,json
sys.path.insert(0,'/home/user/degree-diameter/research/squads/gqd5-r1/c2')
from orb import *
import networkx as nx
HERE='/home/user/degree-diameter/research/squads/gqd5-r1/c2/'
seed=int(sys.argv[1]); ntr=int(sys.argv[2]); dlist=[int(x) for x in sys.argv[3].split(',')]
per_d=int(sys.argv[4]) if len(sys.argv)>4 else 10**9
log=open(HERE+'run2_%d.log'%seed,'a')
def L(*a): print(*a,file=log,flush=True)
def mwc(good):
    n=len(good)
    if n==0: return 0,[]
    orb_id=np.full(N,-1,dtype=np.int64)
    for i,o in enumerate(good): orb_id[o]=i
    r,c=np.nonzero(COL); a,b=orb_id[r],orb_id[c]; m=(a>=0)&(b>=0)&(a!=b)
    OC=np.zeros((n,n),bool); OC[a[m],b[m]]=True; OC=OC|OC.T
    G=nx.Graph()
    for i in range(n): G.add_node(i,weight=len(good[i]))
    ii,jj=np.nonzero(np.triu(~OC,1))
    G.add_edges_from(zip(ii.tolist(),jj.tolist()))
    cl,w=nx.max_weight_clique(G,weight='weight')
    S=sorted(int(x) for i in cl for x in good[i])
    return w,S
rng=random.Random(seed)
cnt={d:0 for d in dlist}
best={}
for trial in range(ntr):
    g=random_symp(rng,k=rng.randrange(2,14)); m=order_of(g)
    if m is None or m==1: continue
    for d in dlist:
        if m%d or cnt[d]>=per_d: continue
        cnt[d]+=1
        h=mpow(g,m//d); orbs=orbits_of_perm(perm_of(h)); good=usable_orbits(orbs)
        prof=tuple(sorted(len(o) for o in orbs))
        t=time.time(); sz,S=mwc(good)
        L('d',d,'elem',m,'orbits',len(orbs),'usable',len(good),'score',sz,'time',round(time.time()-t,2),'profile',prof[:0] if len(prof)>0 else '', 'sizes', sorted(set(len(o) for o in orbs)))
        if sz>best.get('score',0):
            best={'score':sz,'d':d,'S':S}
            json.dump({'size':sz,'order':d,'S':S},open(HERE+'best_run2_%d.json'%seed,'w'))
            L('NEW BEST',sz,'d',d)
L('done',best.get('score'),best.get('d'))
