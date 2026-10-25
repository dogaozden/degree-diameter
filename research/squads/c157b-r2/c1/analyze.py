import sys, numpy as np
SH='/home/user/degree-diameter/research/squads/c157b-r2/shared/'
b=open(SH+'hex_q11.bin','rb').read()
q,N,Lc=(int(x) for x in np.frombuffer(b[:12],dtype=np.int32)); Q1=q+1
LP=np.frombuffer(b[12:12+4*Lc*Q1],dtype=np.int32).reshape(Lc,Q1).astype(np.int64)
fl=np.repeat(np.arange(Lc),Q1); PL=fl[np.lexsort((fl,LP.reshape(-1)))].reshape(N,Q1)
ld=lambda f: np.loadtxt(f,dtype=np.int64).reshape(-1)
allow=np.zeros(N,bool); allow[ld(SH+'allow_P2.txt')]=True
print('N',N,'Lc',Lc,'allow_P2 size',allow.sum())
for name in sys.argv[1:]:
    f=name if name.startswith('/') else SH+name
    s=ld(f); m=np.zeros(N,bool); m[s]=True
    cnt=m[PL].sum(1)            # chosen points per line? (PL: point->lines) -> need line counts
    lc=m[LP].sum(1)             # chosen points on each line
    print(name,'size',len(s),'unique',len(np.unique(s)),'max per line',lc.max(),'lines with 2:',(lc==2).sum(),'lines with 3+',(lc>=3).sum())
    # points: number of chosen collinear partners (lines with lc==2 through point)
    pl=(lc[PL]==2)&m[PL]   # for chosen point x: lines through x with exactly 2 chosen
    # count of pair-lines through each point
    nb=(lc[PL]>=2).sum(1)  # for every point, lines with >=2 chosen (including own)
    own=m.copy()
    partners=np.where(m, (lc[PL]==2).sum(1), 0)
    print('  chosen points with 1 pair-line:',(partners==1).sum(),' >=2:',(partners>=2).sum())
    paired=m & (partners==1)
    print('  paired elements:',paired.sum(),' paired not in allow:',(paired & ~allow).sum())
    print('  chosen not in allow:',(m & ~allow).sum())
