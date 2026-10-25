import numpy as np, sys, collections, random
sys.path.insert(0,'.'); sys.path.insert(0,'../ovoid')
from hexmod import Hex
import ovlib as L
SP='/tmp/claude-0/-home-user-degree-diameter/0a251e0c-8f17-58ce-a4f2-34eda2ea0db1/scratchpad/'
H=Hex(SP+'hex_q11.bin'); q=11
R=np.load(SP+'R756idx.npy'); S=np.load(SP+'S_herm.npy')
colR=np.zeros(H.N,bool); colR[H.lp[H.pl[R]].reshape(-1)]=True; colR[R]=True
cand=np.nonzero(~colR)[0]
NR=(H.Bmat(cand,R)==0)
rng=random.Random(1)
cnt=collections.Counter()
samp=rng.sample(range(len(cand)),3000)
for i in samp:
    pts=H.X[R[NR[i]]]
    cnt[(int(NR[i].sum()), L._rank(pts.tolist(),q))]+=1
print('(c, rank of span of N(x)) over 3000 candidates:', sorted(cnt.items()))
# identical neighbourhoods among candidates?
keys=collections.Counter(np.packbits(NR,axis=1).tobytes()[j*95:(j+1)*95] for j in range(len(cand)))
print('candidates', len(cand), 'distinct neighbourhoods', len(keys), 'max multiplicity', max(keys.values()))
