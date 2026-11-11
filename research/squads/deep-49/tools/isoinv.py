"""Rough isomorphism invariants for Haar sets: distance distribution from the two roots (both sides) of H(G,S),
computed in the Cayley-like 2-step graphs with T = SS^-1 and S^-1S.  Usage: isoinv.py TABLE HITFILE (lines: c x y z)"""
import sys, numpy as np
from collections import Counter
f=open(sys.argv[1],'rb'); N=int(np.fromfile(f,dtype=np.int32,count=1)[0]); MT=np.fromfile(f,dtype=np.uint16,count=N*N).reshape(N,N).astype(np.int64)
I=np.zeros(N,np.int64); r,c=np.nonzero(MT==0); I[r]=c
def dd(T):
    seen=np.full(N,-1); seen[0]=0; fr=np.array([0]); d=0; out=[1]
    while len(fr):
        nx=np.unique(MT[np.ix_(fr,T)].ravel()); nx=nx[seen[nx]<0]; d+=1; seen[nx]=d; fr=nx
        if len(nx): out.append(len(nx))
    return tuple(out)
inv=Counter()
for line in open(sys.argv[2]):
    p=list(map(int,line.split()));
    if len(p)<4: continue
    S=[0]+p[1:4]
    T1=sorted({int(MT[s,I[t]]) for s in S for t in S}); T2=sorted({int(MT[I[s],t]) for s in S for t in S})
    a,b=dd(T1),dd(T2)
    inv[(p[0],)+tuple(sorted([a,b]))]+=1
for k,v in sorted(inv.items()): print(v,k)
