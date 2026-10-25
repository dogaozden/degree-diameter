import numpy as np
SH='/home/user/degree-diameter/research/squads/c157b-r1/shared/'
b=open(SH+'hex_q11.bin','rb').read()
q,N,L=(int(x) for x in np.frombuffer(b[:12],dtype=np.int32))
X=np.frombuffer(b[12+4*L*(q+1):12+4*L*(q+1)+N*7],dtype=np.uint8).reshape(N,7).astype(np.int64)
Rp=np.loadtxt(SH+'Rp.txt',dtype=np.int64).reshape(-1)
V=X[:,[4,5,6,3,0,1,2]].copy(); V[:,3]=(-2*V[:,3])%q
M=(X[Rp]@V[Rp].T)%q; np.fill_diagonal(M,1)
deg=(M==0).sum(1)
base=Rp[deg<=3]; ext=Rp[deg>3]
print('base',len(base),'extras',len(ext),'pairwise opposite base:', bool((M[np.ix_(deg<=3,deg<=3)]!=0).all()))
np.savetxt('base756.txt',base,fmt='%d'); np.savetxt('extras12.txt',ext,fmt='%d')
