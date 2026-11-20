# Independent construction of the claimed Haar graph H(G,S), G = PSL(2,7) x SL(2,8) x Z7.
# Vertices (g,0),(g,1); (g,0) ~ (g*s,1) for s in S. Writes CSR as int32 binary.
import sys, numpy as np, itertools
conv = sys.argv[1] if len(sys.argv)>1 else "row"   # row: mat(a,b,c,d)=[[a,b],[c,d]]; col: [[a,c],[b,d]]
out = sys.argv[2] if len(sys.argv)>2 else "graph.bin"
# GF(8) = F2[x]/(x^3+x+1), elements 0..7 as bit polys
def gmul(a,b):
    r=0
    for i in range(3):
        if (b>>i)&1: r^=a<<i
    for i in (4,3):
        if (r>>i)&1: r^=0b1011<<(i-3)
    return r
G8=[[gmul(a,b) for b in range(8)] for a in range(8)]
def m8(A,B):
    (a,b,c,d),(e,f,g,h)=A,B
    return (G8[a][e]^G8[b][g], G8[a][f]^G8[b][h], G8[c][e]^G8[d][g], G8[c][f]^G8[d][h])
def m7(A,B):
    (a,b,c,d),(e,f,g,h)=A,B
    return ((a*e+b*g)%7,(a*f+b*h)%7,(c*e+d*g)%7,(c*f+d*h)%7)
def can7(M): 
    N=tuple((-x)%7 for x in M); return min(M,N)
# enumerate groups
P7=sorted({can7(M) for M in itertools.product(range(7),repeat=4) if (M[0]*M[3]-M[1]*M[2])%7==1})
S8=[M for M in itertools.product(range(8),repeat=4) if G8[M[0]][M[3]]^G8[M[1]][M[2]]==1]
assert len(P7)==168 and len(S8)==504, (len(P7),len(S8))
i7={m:i for i,m in enumerate(P7)}; i8={m:i for i,m in enumerate(S8)}
T7=np.array([[i7[can7(m7(a,b))] for b in P7] for a in P7],dtype=np.int32)
T8=np.array([[i8[m8(a,b)] for b in S8] for a in S8],dtype=np.int32)
# claimed generators
txt=open("generators.txt").read().split("\n")[1:]
import re
gens=[]
for ln in txt:
    if not ln.strip(): continue
    nums=list(map(int,re.findall(r"mat\((\d+),(\d+),(\d+),(\d+)\)",ln)[0]))+list(map(int,re.findall(r"mat\((\d+),(\d+),(\d+),(\d+)\)",ln)[1]))
    z=int(re.search(r"z=(\d+)",ln).group(1))
    A=tuple(nums[:4]);B=tuple(nums[4:])
    if conv=="col": A=(A[0],A[2],A[1],A[3]);B=(B[0],B[2],B[1],B[3])
    assert (A[0]*A[3]-A[1]*A[2])%7==1 and G8[B[0]][B[3]]^G8[B[1]][B[2]]==1
    gens.append((i7[can7(A)],i8[B],z))
print("gens",len(gens),"distinct",len(set(gens)))
assert len(set(gens))==10
N=168*504*7
def idx(a,b,z): return (a*504+b)*7+z
A=np.repeat(np.arange(168),504*7); B=np.tile(np.repeat(np.arange(504),7),168); Z=np.tile(np.arange(7),168*504)
nb=np.empty((N,10),dtype=np.int32)
for k,(a,b,z) in enumerate(gens):
    nb[:,k]=(T7[A,a]*504+T8[B,b])*7+(Z+z)%7
# CSR over 2N vertices: side0 = g, side1 = N+g
inv=np.empty((N,10),dtype=np.int32)  # neighbours of (h,1): all g with g*s=h
for k,(a,b,z) in enumerate(gens):
    inv[nb[:,k],k]=np.arange(N,dtype=np.int32)   # needs nb[:,k] to be a permutation
    assert len(np.unique(nb[:,k]))==N
adj=np.concatenate([nb+N,inv],axis=0).astype(np.int32)
adj.tofile(out); print("wrote",adj.shape)
