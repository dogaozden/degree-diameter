import numpy as np, gperm
N=gperm.N; LP=gperm.LP
Rp=np.loadtxt('../w/Rp.txt',dtype=np.int64)
RH=np.loadtxt('RH.txt',dtype=np.int64); RHb=np.loadtxt('RHb.txt',dtype=np.int64)
P0=np.loadtxt('P0.txt',dtype=np.int64); P1=np.loadtxt('P1.txt',dtype=np.int64)
def lncov(pts):
    s=np.zeros(N,bool); s[pts]=True; return s[LP].any(1)
U2B=lncov(np.concatenate([P0,P1,Rp])); U3A=lncov(np.concatenate([RH,RHb,Rp]))
print('lines meeting P0uP1uR\':',U2B.sum(),' meeting RHuRHbuR\':',U3A.sum(),' both',(U2B&U3A).sum())
np.savetxt('allow_S.txt',np.nonzero(U2B&U3A)[0],fmt='%d')
