import sys, numpy as np
hexfn='/home/user/degree-diameter/research/squads/c157b-r2/shared/hex_q11.bin'
b=open(hexfn,'rb').read()
q,N,Lc=(int(x) for x in np.frombuffer(b[:12],dtype=np.int32)); Q1=q+1
LP=np.frombuffer(b[12:12+4*Lc*Q1],dtype=np.int32).reshape(Lc,Q1).astype(np.int64)
flat_p=LP.reshape(-1); flat_l=np.repeat(np.arange(Lc),Q1)
PL=flat_l[np.lexsort((flat_l,flat_p))].reshape(N,Q1)
np.save('/home/user/degree-diameter/research/squads/c157b-r2/c2/LP.npy',LP); np.save('/home/user/degree-diameter/research/squads/c157b-r2/c2/PL.npy',PL)
allow=np.zeros(N,bool)
allow[np.loadtxt('/home/user/degree-diameter/research/squads/c157b-r2/shared/allow_S2.txt',dtype=np.int64).reshape(-1)]=True
for f in sys.argv[1:]:
    S=np.loadtxt(f,dtype=np.int64).reshape(-1)
    s=np.zeros(N,bool); s[S]=True
    # number of S lines concurrent with each line (via points)
    pc=np.zeros(N,np.int64)
    for p in range(N): pass
    cntpt=s[PL].sum(1)  # per point: number of S lines through point
    kc=cntpt[LP].sum(1)-12*s  # per line: S-neighbours
    kc=kc-0
    pairs=(s&(kc==1)).sum()
    viol=(s&(kc>=2)).sum()
    unal=(s&(kc==1)&~allow).sum()
    print(f, 'size',len(S),'unique',len(np.unique(S)),'paired',pairs,'pairs',pairs//2,'violations',viol,'unallowed paired',unal)
