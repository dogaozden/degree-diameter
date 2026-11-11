# Recompute the Q(4,5) family optimum (one ovoid of clones + shadow lines with stand-ins) and print it in coordinates.
import sys, json
from collections import deque
sys.dont_write_bytecode = True
sys.path.insert(0, __import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), '..', '..', 'gq4'))
from gq_clones import q4
import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import lil_matrix
q=5
pts, lines, ovoid = q4(q)
n,m=len(pts),len(lines); O=set(ovoid)
A=lil_matrix((n,m))
for j,L in enumerate(lines):
    for p in L: A[p,j]=1
cap=np.array([2 if p in O else 1 for p in range(n)])
res=milp(-np.ones(m),constraints=[LinearConstraint(A.tocsr(),0,cap)],integrality=np.ones(m),bounds=Bounds(0,1),options={'time_limit':600})
x=np.round(res.x).astype(int); M=[j for j in range(m) if x[j]]
print('|M|=',len(M), res.message)
# build graph with stand-ins: first use of an ovoid point -> the point, second -> its clone
on=[[] for _ in range(n)]
for j,L in enumerate(lines):
    for p in L: on[p].append(n+j)
adj={}
def E(a,b): adj.setdefault(a,set()).add(b); adj.setdefault(b,set()).add(a)
for j,L in enumerate(lines):
    for p in L: E(('P',p),('L',j))
for a in O:
    for Lv in on[a]: E(('C',a),('L',Lv-n))
used=set(); standin={}
for j in M:
    for p in sorted(lines[j]):
        s=('P',p) if ('P',p) not in used else ('C',p)
        assert s not in used; used.add(s); standin[(j,p)]=s; E(s,('S',j))
V=list(adj); N=len(V); print('order',N,'maxdeg',max(len(adj[v]) for v in V))
ix={v:i for i,v in enumerate(V)}; nb=[[ix[u] for u in adj[v]] for v in V]
diam=0
for s in range(N):
    d=[-1]*N; d[s]=0; dq=deque([s])
    while dq:
        u=dq.popleft()
        for w in nb[u]:
            if d[w]<0: d[w]=d[u]+1; dq.append(w)
    assert min(d)>=0; diam=max(diam,max(d))
print('diameter',diam)
def show(p): return '('+':'.join(str(c) for c in pts[p])+')'
out=[]
for j in M:
    L=sorted(lines[j])
    out.append({'line':[pts[p] for p in L],'clone_standins':[pts[p] for p in L if standin[(j,p)][0]=='C']})
    print(' '.join(show(p)+('*' if standin[(j,p)][0]=='C' else '') for p in L))
json.dump(out,open(__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)),'q4_359_lines.json'),'w'))
twice=[p for p in O if sum(1 for j in M if p in lines[j])==2]
print('ovoid points on two shadow lines:',len(twice),[show(p) for p in twice])
