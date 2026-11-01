"""Read an ExportGroup file and write the hx table (.tab) and automorphism permutations (.aut).
Usage: build_tab.py EXPORTFILE OUTPREFIX"""
import sys, numpy as np
f=open(sys.argv[1]); n,ng=map(int,f.readline().split())
R=[np.array(list(map(int,f.readline().split())),dtype=np.int64) for _ in range(ng)]
na=int(f.readline()); AI=[list(map(int,f.readline().split())) for _ in range(na)]
# BFS: element b = parent[b] * g_k ; table column T[:,b] = R_k[T[:,parent]]
T=np.zeros((n,n),dtype=np.int64); T[:,0]=np.arange(n)
seen=np.zeros(n,bool); seen[0]=True; order=[0]; par={0:None}; 
h=0
while h<len(order):
    p=order[h]; h+=1
    for k in range(ng):
        b=R[k][p]
        if not seen[b]:
            seen[b]=True; order.append(b); par[b]=(p,k); T[:,b]=R[k][T[:,p]]
assert len(order)==n
# check associativity on a sample
rng=np.random.default_rng(0)
for _ in range(2000):
    a,b,c=rng.integers(0,n,3)
    assert T[T[a,b],c]==T[a,T[b,c]]
with open(sys.argv[2]+'.tab','wb') as fo:
    np.array([n],dtype=np.int32).tofile(fo); T.astype(np.uint16).tofile(fo)
perms=[]
for imgs in AI:
    P=np.zeros(n,dtype=np.int64); P[0]=0
    for b in order[1:]:
        p,k=par[b]; P[b]=T[P[p],imgs[k]]
    assert len(set(P.tolist()))==n
    perms.append(P)
with open(sys.argv[2]+'.aut','w') as fo:
    fo.write(f"{len(perms)}\n")
    for P in perms: fo.write(" ".join(map(str,P.tolist()))+"\n")
print(n, ng, "gens;", na, "aut gens")
