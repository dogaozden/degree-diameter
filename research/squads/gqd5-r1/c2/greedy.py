"""Heuristic: randomized greedy + swap local search over orbit unions (weighted independent set in orbit conflict graph)."""
import sys,time,random,json
sys.path.insert(0,'/home/user/degree-diameter/research/squads/gqd5-r1/c2')
from orb import *
HERE='/home/user/degree-diameter/research/squads/gqd5-r1/c2/'
seed=int(sys.argv[1]); ntr=int(sys.argv[2]); dlist=[int(x) for x in sys.argv[3].split(',')]
log=open(HERE+'greedy_%d.log'%seed,'a')
def L(*a): print(*a,file=log,flush=True)
rng=random.Random(seed)
best_all=0
for trial in range(ntr):
    g=random_symp(rng,k=rng.randrange(2,14)); m=order_of(g)
    if m is None or m==1: continue
    for d in dlist:
        if m%d: continue
        h=mpow(g,m//d); orbs=orbits_of_perm(perm_of(h)); good=usable_orbits(orbs)
        n=len(good)
        if n==0: continue
        orb_id=np.full(N,-1,dtype=np.int64)
        for i,o in enumerate(good): orb_id[o]=i
        r,c=np.nonzero(COL); a,b=orb_id[r],orb_id[c]; mm=(a>=0)&(b>=0)&(a!=b)
        OC=np.zeros((n,n),bool); OC[a[mm],b[mm]]=True; OC=OC|OC.T
        nb=[set(np.nonzero(OC[i])[0].tolist()) for i in range(n)]
        w=[len(o) for o in good]
        bestv=0; bestset=None
        for rep in range(300):
            # randomized greedy: weight with noise
            order=sorted(range(n), key=lambda i: -(w[i]+rng.random()*4))
            S=set(); blocked=set()
            for i in order:
                if i in blocked: continue
                S.add(i); blocked|=nb[i]; blocked.add(i)
            val=sum(w[i] for i in S)
            # (1,1)/(1,2)-swap local search: try removing one vertex and adding free ones
            improved=True
            while improved:
                improved=False
                for x in list(S):
                    # vertices whose only conflict inside S is x
                    cand=[y for y in range(n) if y not in S and not (nb[y]&S)-{x} and not (nb[y]&S-{x})]
                    cand=[y for y in range(n) if y not in S and (nb[y]&S)<= {x}]
                    add=[]; blk=set()
                    rng.shuffle(cand)
                    for y in cand:
                        if y in blk or (nb[y]&blk): continue
                        add.append(y); blk.add(y)
                    gain=sum(w[y] for y in add)-w[x]
                    if gain>0:
                        S.discard(x); S|=set(add); improved=True; break
            val=sum(w[i] for i in S)
            if val>bestv:
                bestv=val; bestset=sorted(S)
        Sv=sorted(int(x) for i in bestset for x in good[i])
        ok=is_ok=None
        L('trial',trial,'d',d,'elem',m,'usable',n,'best',bestv)
        if bestv>best_all:
            best_all=bestv
            json.dump({'size':bestv,'order':d,'S':Sv},open(HERE+'best_greedy_%d.json'%seed,'w'))
            L('NEW BEST',bestv,'d',d)
L('done',best_all)
