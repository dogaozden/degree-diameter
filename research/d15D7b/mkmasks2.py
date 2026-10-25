# masks when the non-bottleneck friendly sets are designed afterwards to cover every needed partner:
# points may pair if covered by a level-2 A-line (S3 u S4 u sigma(R')); lines if they meet a level-2 B-point (P0 u P1 u R')
import sys, numpy as np, gperm
N=gperm.N; LP=gperm.LP
ld=lambda f: np.loadtxt(f,dtype=np.int64).reshape(-1)
Rp=ld('../w/Rp.txt'); sig=ld('../w/sigma.txt'); sR=sig[Rp]
P0,P1,S3,S4=(ld(f) for f in sys.argv[1:5])
c=np.zeros(N,bool); c[LP[np.concatenate([S3,S4,sR])].reshape(-1)]=True
s=np.zeros(N,bool); s[np.concatenate([P0,P1,Rp])]=True; mS=s[LP].any(1)
np.savetxt('allow_P2.txt',np.nonzero(c)[0],fmt='%d'); np.savetxt('allow_S2.txt',np.nonzero(mS)[0],fmt='%d')
print('masks: points',c.sum(),'lines',mS.sum())
