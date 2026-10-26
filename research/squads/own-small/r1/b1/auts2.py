import sys, random
from collections import deque
L=open("/home/user/degree-diameter/research/squads/own-small/tools/bases/cubic/gh2.txt").read().split()
n,m=int(L[0]),int(L[1])
E=[(int(L[2+2*i]),int(L[3+2*i])) for i in range(m)]
adj=[set() for _ in range(n)]
for a,b in E: adj[a].add(b); adj[b].add(a)
D=[]
for s in range(n):
    d=[-1]*n; d[s]=0; q=deque([s])
    while q:
        v=q.popleft()
        for w in adj[v]:
            if d[w]<0: d[w]=d[v]+1; q.append(w)
    D.append(d)
order=[0]; seenv={0}; par={0:None}; dq=deque([0])
while dq:
    v=dq.popleft()
    for w in sorted(adj[v]):
        if w not in seenv: seenv.add(w); par[w]=v; order.append(w); dq.append(w)
def order_of(p):
    k=1; q=p[:]
    while q!=list(range(n)):
        q=[p[q[i]] for i in range(n)]; k+=1
    return k
img=[-1]*n; used=[False]*n
found={}
count=0
want=(int(sys.argv[1]), int(sys.argv[2]))  # (order wanted, seed)
random.seed(want[1])
def dfs(i, first):
    global count
    if i==n:
        count+=1
        p=img[:]
        k=order_of(p)
        if k==want[0] and want[0] not in found:
            found[want[0]]=p; return True
        return False
    x=order[i]
    cands=list(range(n)) if i==0 else sorted(adj[img[par[x]]], key=lambda c: random.random())
    for c in cands:
        if used[c]: continue
        ok=True
        for j in range(i):
            y=order[j]
            if D[x][y]!=D[c][img[y]]: ok=False; break
        if not ok: continue
        img[x]=c; used[c]=True
        if dfs(i+1, first): return True
        img[x]=-1; used[c]=False
    return False
ok=dfs(0,None)
print("found" if ok else "none", "auts visited", count)
if ok:
    p=found[want[0]]
    open(f"sigma{want[0]}.perm","w").write(" ".join(map(str,p))+"\n")
