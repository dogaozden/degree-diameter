# Edge list of the connected component of (e,A) in H(G x Z_m, S), G = SL/PSL/PGL(2,q), for all-pairs checks with apsp.c.
# Independent of haar_ecc.c: elements are kept as normalised 2x2 matrices (tuples), products by plain Python arithmetic.
# Usage: python3 component_edges.py sl|psl|pgl q m OUT < gens   (gens: lines "a b c d z")
import sys
from collections import deque
mode,q,m,out=sys.argv[1],int(sys.argv[2]),int(sys.argv[3]),sys.argv[4]
def norm(M):
    a,b,c,d=[x%q for x in M]
    if mode=='pgl':
        lead=a if a else b; t=pow(lead,q-2,q); return tuple(x*t%q for x in (a,b,c,d))
    if mode=='psl':
        lead=a if a else b
        if lead>(q-1)//2: return tuple((-x)%q for x in (a,b,c,d))
    return (a,b,c,d)
def mul(X,Y):
    a,b,c,d=X; e,f,g,h=Y; return (a*e+b*g, a*f+b*h, c*e+d*g, c*f+d*h)
gens=[]
for L in sys.stdin:
    t=L.split()
    if len(t)==5: a,b,c,d,z=map(int,t); gens.append(((a%q,b%q,c%q,d%q),z%m))
I=norm((1,0,0,1)); start=(I,0,'A'); ids={start:0}; dq=deque([start]); edges=[]
while dq:
    v=dq.popleft(); g,z,s=v
    for (M,t) in gens:
        if s=='A': w=(norm(mul(M,g)),(z+t)%m,'B')
        else:
            a,b,c,d=M; Minv=(d,-b,-c,a); w=(norm(mul(Minv,g)),(z-t)%m,'A')
        if w not in ids: ids[w]=len(ids); dq.append(w)
        if s=='A': edges.append((ids[v],ids[w]))
with open(out,'w') as f:
    f.write(f"{len(ids)}\n")
    for u,w in edges: f.write(f"{u} {w}\n")
print("vertices",len(ids),"edges",len(edges))
