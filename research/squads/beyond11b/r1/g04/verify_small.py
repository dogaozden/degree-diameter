# independent check: rebuild Haar graph from affine-map definition of the group, full BFS from both sides
import sys
from collections import deque
path=sys.argv[1]
lines=[l.split() for l in open(path) if l.strip() and not l.startswith('#')]
poly=[int(x) for x in lines[0][1:]]; S=[int(x) for x in lines[1][1:]]
p=int(open(path).readline().split('p=')[1].split()[0]); e=int(open(path).readline().split('e=')[1].split()[0])
k=int(open(path).readline().split('k=')[1].split()[0]) if False else None
hdr=open(path).readline()
q=p**e; k=int(hdr.split(' k=')[1].split()[0]); m=(q-1)//k
def dig(x): return [(x//p**j)%p for j in range(e)]
def und(d): return sum(d[j]*p**j for j in range(e))
def fadd(x,y): return und([(a+b)%p for a,b in zip(dig(x),dig(y))])
def fmul(x,y):
    # polynomial product mod x^e + sum poly[j] x^j
    a=dig(x); b=dig(y); r=[0]*(2*e)
    for i in range(e):
        for j in range(e): r[i+j]=(r[i+j]+a[i]*b[j])%p
    for d in range(2*e-1,e-1,-1):
        t=r[d]; r[d]=0
        for j in range(e): r[d-e+j]=(r[d-e+j]-t*poly[j])%p
    return und(r[:e])
# zeta: element x (primitive); find its powers
zeta=p if e>=2 else (-poly[0])%p
pw=[1]
for _ in range(q-2): pw.append(fmul(pw[-1],zeta))
assert len(set(pw))==q-1, "not primitive"
def a_of(i): return pw[(i*m)%(q-1)] if (i*m)%(q-1)!=0 else 1
# group elements as (ai, b) with ai = a value
def idx(i,b): return i*q+b
def elem(g): i,b=divmod(g,q); return (a_of(i),b)
def mul(g,h):
    a,b=elem(g); a2,b2=elem(h)
    A=fmul(a,a2); B=fadd(fmul(a,b2),b)
    # map back to index
    i=pw.index(A)//m
    return idx(i,B)
N=q*k
Sset=S
# edges: (g,A)-(s g,B)
nb={}
V=2*N
adj=[[] for _ in range(V)]
for g in range(N):
    for s in Sset:
        h=mul(s,g)
        adj[g].append(N+h); adj[N+h].append(g)
def ecc(src):
    d=[-1]*V; d[src]=0; dq=deque([src])
    while dq:
        v=dq.popleft()
        for u in adj[v]:
            if d[u]<0: d[u]=d[v]+1; dq.append(u)
    return max(d), sum(1 for x in d if x>=0)
print("python check: ecc(eA), reached, ecc(eB), reached:", ecc(0), ecc(N))
