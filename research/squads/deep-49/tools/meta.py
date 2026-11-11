"""Metacyclic group Z_m x|_r Z_k, element (a,j) indexed a + m*j, product (a,j)(b,l) = (a + r^j b, j+l).
Haar graph H(G,S): (g,A) ~ (s g, B). Same-side words from root (e,A): s^-1 t ... ; we just compute both sides."""
import numpy as np
def table(m,k,r):
    N=m*k; rp=[pow(r,j,m) for j in range(k)]
    a=np.arange(N)%m; j=np.arange(N)//m
    A=a[:,None]; J=j[:,None]; B=a[None,:]; L=j[None,:]
    rpj=np.array(rp)[J]
    MT=((A+rpj*B)%m + m*((J+L)%k)).astype(np.int32)
    return MT
def inv(MT):
    N=MT.shape[0]; e=0
    I=np.zeros(N,dtype=np.int32)
    r,c=np.nonzero(MT==e); I[r]=c; return I
def ball(MT,T,rad):
    N=MT.shape[0]; seen=np.zeros(N,bool); seen[0]=True; fr=np.array([0]); 
    for _ in range(rad):
        nx=np.unique(MT[np.ix_(fr,T)].ravel()); nx=nx[~seen[nx]]; seen[nx]=True; fr=nx
    return seen
def far(MT,S,D=9):
    I=inv(MT); S=list(S)
    T1=sorted({int(MT[I[s],t]) for s in S for t in S})  # S^-1 S
    T2=sorted({int(MT[s,I[t]]) for s in S for t in S})  # S S^-1
    h=(D-1)//2
    b1=ball(MT,T1,h); b2=ball(MT,T2,h)
    return np.nonzero(~b1)[0], np.nonzero(~b2)[0]
