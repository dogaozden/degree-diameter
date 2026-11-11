# Numeric check of Lemmas 1.5 and 1.6 of OMEGA_NOTE on H(q) built by hexq6.c (branch claude/own-12-8-cell-ig5jhd,
# research/d12D8/omega/hexq6.c): python3 lem16.py q hq.txt. 40 sources (points and lines) against every element of
# the same type; orthogonality (b(x,y)=0 iff d<=4) for prime q only.
import sys
from collections import deque
q=int(sys.argv[1]); f=open(sys.argv[2])
_,npt,nl=map(int,f.readline().split())
lines=[list(map(int,f.readline().split())) for _ in range(nl)]
P=[list(map(int,f.readline().split()[1:])) for _ in range(npt)]
n=npt+nl; adj=[[] for _ in range(n)]
for i,l in enumerate(lines):
    for p in l: adj[p].append(npt+i); adj[npt+i].append(p)
def bfs(s):
    d=[-1]*n; d[s]=0; Q=deque([s])
    while Q:
        u=Q.popleft()
        for w in adj[u]:
            if d[w]<0: d[w]=d[u]+1; Q.append(w)
    return d
# polar form for prime q (q=3,5); q=4 uses char 2 tables -> skip ortho check there
srcs=list(range(0,n,max(1,n//40)))
D={s:bfs(s) for s in range(n)} if n<3000 else None
res={}
for t in srcs:
    dt=D[t] if D else bfs(t)
    opp=[x for x in range(n) if dt[x]==6]
    for z in range(n):
        if (z<npt)!=(t<npt): continue
        dz=D[z] if D else bfs(z)
        for R in (2,4):
            c=sum(1 for x in opp if dz[x]<=R)
            res.setdefault((R,dt[z]),set()).add(c)
print("q=%d Lemma 1.6 check, |B(z,R)∩opp(t)| by (R, d(t,z)):"%q, {k:sorted(v) for k,v in sorted(res.items())})
if q in (3,5):
    def b(x,y): return (x[0]*y[4]+x[4]*y[0]+x[1]*y[5]+x[5]*y[1]+x[2]*y[6]+x[6]*y[2]-2*x[3]*y[3])%q
    bad=0
    for t in srcs:
        if t>=npt: continue
        dt=D[t] if D else bfs(t)
        for s in range(npt):
            if (b(P[t],P[s])==0) != (dt[s]<=4): bad+=1
    print("orthogonality mismatches:",bad)
