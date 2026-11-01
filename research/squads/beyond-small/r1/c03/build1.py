import numpy as np, pickle, sys
HALF=16896; W=264
balls=np.fromfile('ball3.bin',dtype=np.uint64).reshape(HALF,W)
G,dirs,lines=pickle.load(open('groups.pkl','rb'))
groups=[51933, 349120, 65280, 43520]
NB=sorted({int(b) for g in groups for b in G[g]})
print('B-neighbours', len(NB), NB)
u=np.bitwise_or.reduce(balls[NB],axis=0)
print('covered A', int(np.unpackbits(u.view(np.uint8)).sum()), 'of', HALF)
src='/home/user/degree-diameter/research/squads/beyond-small/data/d16D5_n33792.edges'
lines_=open(src).read().split('\n')
n=33792+1
out=[str(n)]+lines_[1:]
out=[l for l in out if l.strip()]
hub=33792
out += [f"{hub} {HALF+b}" for b in NB]
open('best_n33793.edges','w').write('\n'.join(out)+'\n')
print('wrote', n)
