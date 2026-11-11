"""Write the Haar graph H(G,S) as an edge list (first line n, then "u v"), A = g (0..N-1), B = N + g,
edges (g,A) ~ (g s, B).  G from an hx table file.  Usage: haar_edges.py TABLE OUT s1 s2 s3 s4"""
import sys, numpy as np
f=open(sys.argv[1],'rb'); N=int(np.fromfile(f,dtype=np.int32,count=1)[0]); MT=np.fromfile(f,dtype=np.uint16,count=N*N).reshape(N,N)
S=list(map(int,sys.argv[3:]))
with open(sys.argv[2],'w') as o:
    o.write(f"{2*N}\n")
    for g in range(N):
        for s in S: o.write(f"{g} {N+int(MT[g,s])}\n")
