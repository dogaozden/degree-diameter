# Affine-line groups: B-vertices (q, y + lam*c), lam in F4, q = controller B-vertex 0..65, y,c in F4^4 (ids 0..255).
import numpy as np, itertools, pickle
W=264; HALF=16896
balls = np.fromfile('ball3.bin', dtype=np.uint64).reshape(HALF, W)
MUL = [[0,0,0,0],[0,1,2,3],[0,2,3,1],[0,3,1,2]]
def vec(i): return [i&3,(i>>2)&3,(i>>4)&3,(i>>6)&3]
def idv(v): return v[0]|(v[1]<<2)|(v[2]<<4)|(v[3]<<6)
def smul(lam,c): return idv([MUL[lam][x] for x in vec(c)])
# canonical directions: one per F4-line through 0
dirs=[]; seen=set()
for c in range(1,256):
    if c in seen: continue
    orb={smul(l,c) for l in range(1,4)}
    seen |= orb|{c}; dirs.append(c)
print('directions', len(dirs))
lines=set()
for c in dirs:
    mc=[smul(l,c) for l in range(4)]
    for y in range(256):
        L=tuple(sorted(y^m for m in mc))
        lines.add((c,L))
lines=sorted(lines, key=lambda t:(t[0],t[1]))
print('affine lines per controller vertex', len(lines))
# group list: (q, c, members)
G=[]
for q in range(66):
    for c,L in lines:
        G.append([q*256+y for y in L])
G=np.array(G,dtype=np.int32)
print('groups', G.shape)
pickle.dump((G,dirs,lines), open('groups.pkl','wb'))
# union coverage per group
cov=np.zeros(len(G),dtype=np.int32)
CH=20000
for s in range(0,len(G),CH):
    g=G[s:s+CH]
    u=np.bitwise_or.reduce(balls[g],axis=1)
    b=np.unpackbits(u.view(np.uint8),axis=1).sum(axis=1)
    cov[s:s+CH]=b
np.save('groupcov.npy',cov)
print('group union coverage: max',cov.max(),'mean',cov.mean(), 'top 10', sorted(cov)[-10:])
