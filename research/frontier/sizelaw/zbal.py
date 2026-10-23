"""Fiber-load excess for G = Q x Z_n: W_z = number of non-backtracking binding words with Z_n-value z.
eps_Z = sum_z |Q| exp(-W_z/|Q|) / (N exp(-W/N)) >= 1 (Jensen); = 1 iff loads are equal."""
import numpy as np, math, glob, re, os, sys
from data import W, mu
def loads(z, n, D):
    d=len(z); z=np.array(z)%n
    # cnt[i, v]: words ending with letter i, current value v; sign of next letter alternates
    tot=np.zeros(n)
    if D%2==0: lengths=range(1,D,2)
    else: lengths=range(2,D,2); tot[0]+=1
    cnt=np.zeros((d,n))
    for i in range(d): cnt[i,z[i]]+=1        # length 1, sign +
    L=1
    if 1 in lengths: tot+=cnt.sum(0)
    while L < D-1:
        sign = -1 if L%2==1 else 1             # letter L+1 has sign (-1)^L
        new=np.zeros((d,n)); allv=cnt.sum(0)
        for j in range(d):
            src=allv-cnt[j]                    # previous letter != j
            new[j]=np.roll(src, sign*z[j])
        cnt=new; L+=1
        if L in lengths: tot+=cnt.sum(0)
    return tot
def epsZ(z,n,D,N):
    w=loads(z,n,D); Qn=N/n; Wt=w.sum()
    return float(np.sum(Qn*np.exp(-(w-Wt/n)/Qn))/N), Wt
if __name__=='__main__':
    FR=os.path.expanduser('~/AI_Projects/degree-diameter/research/frontier/sols')
    rng=np.random.default_rng(0)
    for f in sorted(glob.glob(FR+'/*.txt')):
        h=open(f).readline().split(); d,D=int(h[0]),int(h[1]); n=int(h[h.index('n')+1]); N=int(h[h.index('N')+1])
        if n==1: continue
        z=[int(re.search(r'z=(\d+)',l).group(1)) for l in open(f).readlines()[1:]]
        e,Wt=epsZ(z,n,D,N); assert Wt==W(d,D), (Wt,W(d,D))
        r=[epsZ([0]+list(rng.integers(0,n,d-1)),n,D,N)[0] for _ in range(200)]
        print('%-34s n=%3d eps_Z(record)=%.3f  random z: median %.2f p10 %.2f min %.3f'%(os.path.basename(f)[:-4],n,e,np.median(r),np.percentile(r,10),min(r)))
