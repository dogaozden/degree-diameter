import sys, numpy as np, gperm
N=gperm.N; LP=gperm.LP
ld=lambda f: np.loadtxt(f,dtype=np.int64).reshape(-1)
Rp=ld('../w/Rp.txt'); sig=ld('../w/sigma.txt'); sR=sig[Rp]
RH,RHb,RL,RLb=ld('RH.txt'),ld('RHb.txt'),ld('RL.txt'),ld('RLb.txt')
P0,P1,S3,S4=(ld(f) for f in sys.argv[1:5])
def ptcov(lines):
    c=np.zeros(N,bool); c[LP[lines].reshape(-1)]=True; return c
def lncov(pts):
    s=np.zeros(N,bool); s[pts]=True; return s[LP].any(1)
mP=ptcov(np.concatenate([RL,RLb,sR]))&ptcov(np.concatenate([S3,S4,sR]))
mS=lncov(np.concatenate([P0,P1,Rp]))&lncov(np.concatenate([RH,RHb,Rp]))
np.savetxt('allow_P_ex.txt',np.nonzero(mP)[0],fmt='%d'); np.savetxt('allow_S_ex.txt',np.nonzero(mS)[0],fmt='%d')
print('exact masks: points',mP.sum(),'lines',mS.sum())
