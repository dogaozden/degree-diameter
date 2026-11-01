import numpy as np, pickle, sys
W=264; HALF=16896
balls = np.fromfile('ball3.bin', dtype=np.uint64).reshape(HALF, W)
G,dirs,lines=pickle.load(open('groups.pkl','rb'))
cov=np.load('groupcov.npy')
def pc(u): return int(np.unpackbits(u.view(np.uint8)).sum())
def gunion(gi): return np.bitwise_or.reduce(balls[G[gi]],axis=0)
full=np.zeros(HALF,dtype=np.uint8); full[:]=1
unc=np.packbits(full,bitorder='little').view(np.uint64).copy()
def best_group(unc, CH=20000):
    best=(-1,-1)
    for s in range(0,len(G),CH):
        g=G[s:s+CH]
        u=np.bitwise_or.reduce(balls[g],axis=1) & unc[None,:]
        b=np.unpackbits(u.view(np.uint8),axis=1).sum(axis=1)
        i=int(b.argmax())
        if b[i]>best[0]: best=(int(b[i]), s+i)
    return best
rng=np.random.default_rng(int(sys.argv[1]) if len(sys.argv)>1 else 0)
# greedy from several random starts: first group random among top-coverage
top=np.argsort(-cov)[:2000]
results=[]
for trial in range(int(sys.argv[2]) if len(sys.argv)>2 else 5):
    unc=np.packbits(full,bitorder='little').view(np.uint64).copy()
    chosen=[]
    first=int(rng.choice(top))
    chosen.append(first); unc &= ~gunion(first)
    for step in range(3):
        g,i=best_group(unc)
        chosen.append(i); unc &= ~gunion(i)
    left=pc(unc)
    # spare: best single ball
    gain=np.unpackbits((balls & unc[None,:]).view(np.uint8),axis=1).sum(axis=1)
    k=int(gain.argmax())
    print('trial',trial,'groups',chosen,'left after 4 groups',left,'best spare gain',int(gain[k]),'left after spare',left-int(gain[k]),flush=True)
    results.append((left,chosen,k))
pickle.dump(results,open('gsearch_%s.pkl'%(sys.argv[1] if len(sys.argv)>1 else '0'),'wb'))
