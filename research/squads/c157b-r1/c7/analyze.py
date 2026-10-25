import numpy as np, sys
SH='/home/user/degree-diameter/research/squads/c157b-r1/shared/'
b=open(SH+'hex_q11.bin','rb').read()
q,N,L=(int(x) for x in np.frombuffer(b[:12],dtype=np.int32))
off=12+4*L*(q+1)
LP=np.frombuffer(b[12:off],dtype=np.int32).reshape(L,q+1)
X=np.frombuffer(b[off:off+N*7],dtype=np.uint8).reshape(N,7).astype(np.int64)
Rp=np.loadtxt(SH+'Rp.txt',dtype=np.int64).reshape(-1); sig=np.loadtxt(SH+'sigma.txt',dtype=np.int64).reshape(-1)
print('q',q,'N',N,'L',L,'|Rp|',len(Rp))
def B(I,J):
    x=X[I]; y=X[J][:,[4,5,6,3,0,1,2]].copy(); y[:,3]=(-2*y[:,3])%q
    return (x@y.T)%q
M=B(Rp,Rp)
np.fill_diagonal(M,1)
zero=(M==0)
deg=zero.sum(1)
print('orthogonal (B=0) pairs in Rp (off-diagonal, counted once):',zero.sum()//2)
print('degree histogram (B=0 partners within Rp):',np.bincount(deg)[:40].tolist(), 'max',deg.max())
print('points with deg>0:',(deg>0).sum())
# spread test: lines with all points in x0+x4=0
hyp=((X[:,0]+X[:,4])%q==0)
Sl=np.nonzero(hyp[LP].all(1))[0]
print('lines inside hyperplane x0+x4=0:',len(Sl))
