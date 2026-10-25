# Corollary C1 directly in W(3,q), field model PG(3,q) = E*/F*, E = GF(q^4), q = p prime.
# W(3,q): B(x,y) = Tr_{E/F}(d x y^{q^2}), d = g^{(q^2+1)/2}. 2-ovoid O = C_0 u C_q (index mod q+1).
# Spread: the K-lines {g^{i+(q^2+1)k}}. Graph: incidence graph + one copy of each point of O (joined to the
# t.i. lines on it) + two copies of each spread line (joined to its q+1 points). Check: degrees, diameter 4.
import itertools, sys
from collections import deque
p=int(sys.argv[1]); q=p
def polymulmod(a,b,mod):
    r=[0]*7
    for i in range(4):
        for j in range(4): r[i+j]=(r[i+j]+a[i]*b[j])%p
    for k in range(6,3,-1):
        c=r[k]
        if c:
            for t in range(5): r[k-4+t]=(r[k-4+t]-c*mod[t])%p
    return tuple(r[:4])
def find_prim():
    for c in itertools.product(range(p),repeat=4):
        mod=list(c)+[1]  # x^4 + c3 x^3 + ... monic, coefficients low->high
        if c[0]==0: continue
        x=(0,1,0,0); e=(1,0,0,0); seen=set()
        cur=e; order=None
        for k in range(1,p**4):
            cur=polymulmod(cur,x,mod)
            if cur==e: order=k; break
        if order==p**4-1: return mod
mod=find_prim()
Q4=p**4; pw=[(1,0,0,0)]
for k in range(1,Q4-1): pw.append(polymulmod(pw[-1],(0,1,0,0),mod))
Nn=(q**4-1)//(q-1)
def norm(v):
    for c in v:
        if c: inv=pow(c,p-2,p); return tuple((x*inv)%p for x in v)
pt={}; ptv=[]
for i in range(Nn):
    v=norm(pw[i]); pt[v]=i; ptv.append(pw[i])
assert len(pt)==Nn
def tr(j):  # Tr_{E/F}(g^j), returned as element of F (the constant coefficient after summing)
    s=[0,0,0,0]
    for e in range(4):
        v=pw[(j*q**e)%(Q4-1)]
        s=[(a+b)%p for a,b in zip(s,v)]
    assert s[1]==s[2]==s[3]==0
    return s[0]
dexp=(q*q+1)//2
def B(i,k): return tr(dexp+i+k*q*q)
lines=set()
for i in range(Nn):
    for k in range(Nn):
        if k!=i and B(i,k)==0:
            P=ptv[i]; Qv=ptv[k]
            L={i,k}
            for t in range(p):
                L.add(pt[norm(tuple((a*t+b)%p for a,b in zip(P,Qv)))])
            lines.add(frozenset(L))
lines=list(lines); assert len(lines)==Nn, len(lines)
for L in lines: assert len(L)==q+1
O={i for i in range(Nn) if i%(q+1) in (0,q)}
for L in lines: assert len(L&O)==2
K=q*q+1
spread={frozenset((i+K*k)%Nn for k in range(q+1)) for i in range(Nn)}
assert len(spread)==q*q+1
ls=set(lines)
for s in spread: assert s in ls
adj=[[] for _ in range(Nn)]
for j,L in enumerate(lines):
    adj.append(list(L))
    for x in L: adj[x].append(Nn+j)
lineid={L:Nn+j for j,L in enumerate(lines)}
for x in sorted(O):
    c=len(adj); onl=[l for l in adj[x]]; adj.append(onl)
    for l in onl: adj[l].append(c)
for s in spread:
    for rep in range(2):
        c=len(adj); adj.append(list(s))
        for x in s: adj[x].append(c)
n=len(adj); print('q',q,'order',n,'expected',2*(q*q+1)*(q+3),'degrees',sorted({len(a) for a in adj}))
diam=0
for s0 in range(n):
    dist=[-1]*n; dist[s0]=0; dq=deque([s0])
    while dq:
        u=dq.popleft()
        for v in adj[u]:
            if dist[v]<0: dist[v]=dist[u]+1; dq.append(v)
    assert min(dist)>=0; diam=max(diam,max(dist))
print('diameter',diam)
