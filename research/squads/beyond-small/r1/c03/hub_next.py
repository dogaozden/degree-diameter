import numpy as np, pickle, sys, time, os
HALF=16896; W=264
balls=np.fromfile('ball3.bin',dtype=np.uint64).reshape(HALF,W)
G,dirs,lines=pickle.load(open('groups.pkl','rb'))
cov=np.load('groupcov.npy')
exec(open('hubs.py').read().split("if __name__")[0].split("cov=np.load('groupcov.npy')")[1].replace("def hub_B","def hub_B"), globals()) if False else None
edges=[tuple(map(int,l.split())) for l in open('/home/user/degree-diameter/research/squads/beyond-small/data/d16D5_n33792.edges').read().split('\n')[1:] if l.strip()]
Aadj=[[] for _ in range(HALF)]; Badj=[[] for _ in range(HALF)]
for u,v in edges:
    if u<HALF and v>=HALF: Aadj[u].append(v-HALF); Badj[v-HALF].append(u)
full=np.zeros(HALF,dtype=np.uint8); full[:]=1
ALLA=np.packbits(full,bitorder='little').view(np.uint64).copy()
def pc(u): return int(np.unpackbits(u.view(np.uint8)).sum())
def pair_ok(NB1, NB2):
    s1=set(NB1)
    if s1 & set(NB2): return False
    for b2 in NB2:
        for a in Badj[b2]:          # A-neighbours of B-vertex b2
            for b1 in Aadj[a]:      # B-neighbours of A-vertex a
                if b1 in s1: return True
    return False
state='state.pkl'
hubs,used = pickle.load(open(state,'rb')) if os.path.exists(state) else ([],np.zeros(HALF,dtype=bool))
if not hubs:
    hubs=[sorted({int(b) for g in [51933,349120,65280,43520] for b in G[g]})]
    used[:]=False; used[hubs[0]]=True
    pickle.dump((hubs,used),open(state,'wb'))
t0=time.time()
seed=int(sys.argv[1]) if len(sys.argv)>1 else 0
rng=np.random.default_rng(seed)
cand=np.nonzero(used[G].any(axis=1)==False)[0]
print('candidate groups', len(cand), flush=True)
# restrict to decent groups for speed
cand=cand[np.argsort(-cov[cand])][:4000]
Gc=G[cand]
for attempt in range(40):
    if time.time()-t0>80: break
    unc=ALLA.copy(); chosen=[]
    avail=np.ones(len(cand),dtype=bool)
    for step in range(4):
        u=np.bitwise_or.reduce(balls[Gc],axis=1) & unc[None,:]
        gain=np.unpackbits(u.view(np.uint8),axis=1).sum(axis=1).astype(np.int64)
        gain[~avail]=-1
        if attempt>0:
            top=np.argsort(-gain)[:30]; i=int(rng.choice(top))
        else:
            i=int(gain.argmax())
        if gain[i]<=0: break
        chosen.append(i); avail[i]=False
        unc &= ~np.bitwise_or.reduce(balls[Gc[i]],axis=0)
        # remove groups overlapping chosen B-vertices
        mem=set(Gc[i].tolist())
        conflict=np.isin(Gc,list(mem)).any(axis=1)
        avail &= ~conflict
        if pc(unc)==0: break
    if pc(unc)==0:
        NB=sorted({int(b) for c in chosen for b in Gc[c]})
        if len(NB)>17: continue
        if all(pair_ok(NB,h) for h in hubs) and not (set(NB)&set().union(*[set(h) for h in hubs])):
            hubs.append(NB); used[NB]=True
            pickle.dump((hubs,used),open(state,'wb'))
            print('ADDED hub',len(hubs),'attempt',attempt,'nbrs',len(NB),flush=True)
            break
        else:
            print('cover found but pair/overlap failed attempt',attempt,flush=True)
print('hubs now', len(hubs), 'time', round(time.time()-t0,1))
