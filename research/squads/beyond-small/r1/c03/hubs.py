# Build A-side hubs: each hub = 4 affine groups (16 B-neighbours), pairwise-disjoint B-neighbourhoods.
import numpy as np, pickle, sys
HALF=16896; W=264; NV=33792
balls=np.fromfile('ball3.bin',dtype=np.uint64).reshape(HALF,W)
G,dirs,lines=pickle.load(open('groups.pkl','rb'))
cov=np.load('groupcov.npy')
edges=[tuple(map(int,l.split())) for l in open('/home/user/degree-diameter/research/squads/beyond-small/data/d16D5_n33792.edges').read().split('\n')[1:] if l.strip()]
Aadj=[[] for _ in range(HALF)]; Badj=[[] for _ in range(HALF)]
for u,v in edges:
    if u<HALF: Aadj[u].append(v-HALF)   # A-vertex u adjacent to B index v-HALF
    else: Badj[u-HALF].append(v) if False else None
for u,v in edges:
    if v>=HALF and u<HALF: pass
Badj=[[] for _ in range(HALF)]
for u,v in edges:
    if u<HALF and v>=HALF: Badj[v-HALF].append(u)
Aset=[set(x) for x in Aadj]
full=np.zeros(HALF,dtype=np.uint8); full[:]=1
ALLA=np.packbits(full,bitorder='little').view(np.uint64).copy()
def pc(u): return int(np.unpackbits(u.view(np.uint8)).sum())
def find_cover(unused, maxg=4, CH=40000):
    """unused: bool array over B indices. Greedy over affine groups whose members are all unused."""
    ok = unused[G].all(axis=1)
    idx = np.nonzero(ok)[0]
    unc = ALLA.copy(); chosen=[]
    for step in range(maxg):
        best=(-1,-1)
        for s in range(0,len(idx),CH):
            gi=idx[s:s+CH]
            u=np.bitwise_or.reduce(balls[G[gi]],axis=1) & unc[None,:]
            b=np.unpackbits(u.view(np.uint8),axis=1).sum(axis=1)
            i=int(b.argmax())
            if b[i]>best[0]: best=(int(b[i]), int(gi[i]))
        if best[0]<=0: break
        chosen.append(best[1]); unc &= ~np.bitwise_or.reduce(balls[G[best[1]]],axis=0)
        if pc(unc)==0: break
    return chosen, pc(unc)
def hub_B(chosen):
    return sorted({int(b) for g in chosen for b in G[g]})
def pair_ok(NB1, NB2):
    # exists b in NB1, b' in NB2 with dist(b,b') <= 2 (equal or sharing an A-neighbour)
    s1=set(NB1); s2=set(NB2)
    if s1 & s2: return False
    for b2 in NB2:
        for a in Aadj[b2]:
            for b1 in Badj[a]:
                if b1 in s1: return True
    return False
if __name__=='__main__':
    nh=int(sys.argv[1]); side=sys.argv[2] if len(sys.argv)>2 else 'A'
    unused=np.ones(HALF,dtype=bool)
    hubs=[]
    tries=0
    while len(hubs)<nh and tries<200:
        tries+=1
        chosen,left=find_cover(unused)
        if left>0 or len(chosen)>4:
            print('no cover from unused pool, left',left,'groups',len(chosen),flush=True); break
        NB=hub_B(chosen)
        if len(NB)>17: print('too many nbrs',len(NB)); break
        if any(not pair_ok(NB,h) for h in hubs):
            print('pair condition failed for candidate; skipping, trying again with this group removed')
            # remove the chosen groups' members from pool so a different cover is searched next
            for b in NB: unused[b]=False
            continue
        hubs.append(NB)
        for b in NB: unused[b]=False
        print('hub',len(hubs),'nbrs',NB,flush=True)
    pickle.dump(hubs,open('hubs_%s.pkl'%side,'wb'))
    print('hubs found', len(hubs), 'B-vertices used', sum(len(h) for h in hubs), 'remaining unused', int(unused.sum()))
