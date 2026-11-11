"""Independent check (numpy-free BFS-style products) of Haar sets S={0,x,y,z} in a table file.
usage: check_sets.py TABLE SETSFILE(optional lines 'cost x y z' or 'x y z') [MUST]"""
import sys, numpy as np
def load(path):
    with open(path,'rb') as f:
        N=int(np.fromfile(f,dtype=np.int32,count=1)[0])
        MT=np.fromfile(f,dtype=np.uint16,count=N*N).reshape(N,N).astype(np.int64)
    inv=np.zeros(N,dtype=np.int64)
    for a in range(N):
        inv[a]=int(np.where(MT[a]==0)[0][0])
    return N,MT,inv
def sides(N,MT,inv,S):
    A=set(int(MT[s,inv[t]]) for s in S for t in S)   # S S^-1
    B=set(int(MT[inv[s],t]) for s in S for t in S)   # S^-1 S
    def prod(X,Y):
        return set(int(MT[x,y]) for x in X for y in Y)
    XA=prod(prod(A,A),prod(A,A)); XB=prod(prod(B,B),prod(B,B))   # (SS^-1)^4, (S^-1 S)^4
    return XA, XB
if __name__=='__main__':
    N,MT,inv=load(sys.argv[1])
    must=[int(v) for v in sys.argv[3].split(',')] if len(sys.argv)>3 else []
    lines=[l.split() for l in open(sys.argv[2]) if l.strip()]
    for l in lines[:int(sys.argv[4]) if len(sys.argv)>4 else 10**9]:
        vals=list(map(int,l))
        if len(vals)==4: vals=vals[1:]
        x,y,z=vals
        S=[0,x,y,z]
        XA,XB=sides(N,MT,inv,S)
        mA=N-len(XA); mB=N-len(XB)
        mustok=all(g in XA and g in XB for g in must)
        print(x,y,z,'missA',mA,'missB',mB,'cost',mA+mB,'must_ok',mustok, 'missA_has0', [g for g in range(N) if g not in XA][:6])
