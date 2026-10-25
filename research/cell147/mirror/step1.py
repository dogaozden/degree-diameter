import numpy as np, sys, random, collections
sys.path.insert(0,'.')
from hexmod import Hex
SP='/tmp/claude-0/-home-user-degree-diameter/0a251e0c-8f17-58ce-a4f2-34eda2ea0db1/scratchpad/'
H=Hex(SP+'hex_q11.bin')
R=np.load(SP+'R756idx.npy'); S=np.load(SP+'S_herm.npy'); Sset=set(S.tolist())
Rset=set(R.tolist())
col=np.zeros(H.N,bool)
for r in R: col[list(H.collinear_points(r))]=True
print('points collinear with R:', col.sum())
cand=[p for p in range(H.N) if not col[p] and p not in Rset]
print('candidates non-collinear with R:', len(cand))
# c(x) for candidates
Bm=H.Bmat(np.array(cand),R)
c=(Bm==0).sum(axis=1)
print('c distribution:', sorted(collections.Counter(c.tolist()).items()))
# line profiles for random lines w.r.t. S
random.seed(1)
prof=[]
for l in random.sample(range(H.N),300):
    d2,d4=H.line_ball(l)
    n2=len(d2&Sset); n4=len(d4&Sset); n6=len(Sset)-n2-n4-(1 if l in Sset else 0)
    prof.append((n2,n4,n6,l))
print('S-profile of random lines (n2,n4,n6): min n4',min(p[1] for p in prof),'max n4',max(p[1] for p in prof),'n2 values',sorted(collections.Counter(p[0] for p in prof).items()))
print('examples', prof[:5])
