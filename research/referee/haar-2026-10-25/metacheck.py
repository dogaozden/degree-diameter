# Referee check of the four metacyclic Haar records: BFS from (e,A) and (e,B) in Z_m x|_r Z_k, own code.
import numpy as np
cases = [((5,8),61,80,8,[(0,0),(17,76),(45,49),(0,16),(11,62)]),
         ((5,9),422,35,5,[(0,0),(318,34),(101,22),(327,1),(290,8)]),
         ((4,10),97,64,19,[(0,0),(74,51),(30,20),(47,1)]),
         ((5,10),1989,24,461,[(0,0),(826,18),(423,7),(1635,11),(993,10)]),
         # newer (5,9) graph on master (commit c48c976), not in the note
         ((5,9),346,43,29,[(0,0),(249,8),(58,9),(284,41),(265,16)])]
for (d,D),m,k,r,S in cases:
    assert pow(r,k,m)==1
    N=m*k
    A=np.arange(N)%m; J=np.arange(N)//m           # index = j*m + a
    rp=[pow(r,j,m) for j in range(k)]
    def lm(s):   # s * g
        a,j=s; return ((a+rp[j]*A)%m) + ((j+J)%k)*m
    def inv(s):
        a,j=s; jj=(-j)%k; return ((-rp[jj]*a)%m, jj)
    F=[lm(s) for s in S]; B=[lm(inv(s)) for s in S]
    for P in F+B: assert len(np.unique(P))==N
    assert len(set(S))==d
    ok=True; eccs=[]
    for start in (0,1):
        vis=[np.zeros(N,bool),np.zeros(N,bool)]; vis[start][0]=True
        fr=np.array([0]); side=start; ecc=0
        for step in range(1,D+1):
            T=F if side==0 else B
            nb=np.unique(np.concatenate([P[fr] for P in T])); ns=1-side
            nb=nb[~vis[ns][nb]]; vis[ns][nb]=True
            if len(nb): ecc=step
            fr=nb; side=ns
        ok&= bool(vis[0].all() and vis[1].all()); eccs.append(ecc)
    # also D-1 must fail
    print((d,D),'N',N,'vertices',2*N,'VALID' if ok else 'INVALID','ecc',eccs, 'order of r', next(t for t in range(1,k+1) if pow(r,t,m)==1))
