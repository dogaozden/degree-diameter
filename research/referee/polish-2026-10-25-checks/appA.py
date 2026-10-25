import sys, itertools, re
sys.path.insert(0,'.')
from gf import diam
q=5
Qf=lambda v:(v[0]*v[0]+v[1]*v[2]+v[3]*v[4])%q
def norm(v):
    v=[x%q for x in v]
    for x in v:
        if x: iv=pow(x,-1,q); return tuple((iv*y)%q for y in v)
pts=sorted(set(norm(v) for v in itertools.product(range(q),repeat=5) if any(v) and Qf(v)==0))
assert len(pts)==156
pid={p:i for i,p in enumerate(pts)}
B=lambda u,v:(2*u[0]*v[0]+u[1]*v[2]+u[2]*v[1]+u[3]*v[4]+u[4]*v[3])%q
lines=set()
for i,u in enumerate(pts):
    for j in range(i+1,len(pts)):
        v=pts[j]
        if B(u,v)==0:
            lines.add(frozenset(pid[norm([a+t*b for a,b in zip(u,v)])] for t in range(q))|{j})
lines=sorted(lines,key=sorted); assert len(lines)==156
lid={L:k for k,L in enumerate(lines)}
O=[i for i,p in enumerate(pts) if (p[4]-2*p[3])%q==0]
print("ovoid size",len(O), "each line meets O once:", all(len(L & set(O))==1 for L in lines))
shadow=[]
import os
for row in open(os.path.join(os.path.dirname(os.path.abspath(__file__)),'app_lines.txt')):
    toks=re.findall(r'\(([0-9:]+)\)(\*?)',row)
    ps=[(tuple(int(x) for x in t.split(':')),st=='*') for t,st in toks]
    assert len(ps)==6
    for p,_ in ps: assert p==norm(p) and Qf(p)==0, (row,p)
    L=frozenset(pid[p] for p,_ in ps)
    assert L in lid, ("not a line",row)
    shadow.append((lid[L],[(pid[p],st) for p,st in ps]))
print("21 rows parsed, all are lines of Q(4,5):",len(shadow)==21, "distinct:",len(set(s[0] for s in shadow)))
# intersections
from collections import Counter
cnt=Counter(x for _,ps in shadow for x,_ in ps)
multi={x:c for x,c in cnt.items() if c>1}
print("points on >1 listed line:",[(pts[x],c, x in O) for x,c in multi.items()])
starred=[pts[x] for _,ps in shadow for x,st in ps if st]
print("starred:",starred, "all in O:", all(pid[s] in O for s in starred))
# which rows contain the multi points
for x in multi: print(pts[x],"rows",[k+1 for k,(_,ps) in enumerate(shadow) if any(y==x for y,_ in ps)],"starred in rows",[k+1 for k,(_,ps) in enumerate(shadow) if any(y==x and st for y,st in ps)])
# build graph
nP=156; nL=156; edges=[(x,nP+k) for k,L in enumerate(lines) for x in L]
on=[[] for _ in range(nP)]
for k,L in enumerate(lines):
    for x in L: on[x].append(k)
nxt=nP+nL; clone={}
for o in O:
    clone[o]=nxt
    for k in on[o]: edges.append((nxt,nP+k))
    nxt+=1
for _,ps in shadow:
    for x,st in ps: edges.append(((clone[x] if st else x),nxt))
    nxt+=1
print(diam(nxt,edges))
