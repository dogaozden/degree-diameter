"""Write only the hx multiplication table (int32 n, then n*n uint16) of Z_m x|_r Z_k.  Usage: mktab.py m k r OUTPREFIX"""
import sys, numpy as np
m,k,r=map(int,sys.argv[1:4]); out=sys.argv[4]; N=m*k
assert pow(r,k,m)==1%m
rp=[pow(r,j,m) for j in range(k)]
a=np.arange(N)%m; j=np.arange(N)//m
MT=((a[:,None]+np.array(rp)[j][:,None]*a[None,:])%m + m*((j[:,None]+j[None,:])%k)).astype(np.uint16)
with open(out+'.tab','wb') as f:
    np.array([N],dtype=np.int32).tofile(f); MT.tofile(f)
print(N, "written")
