import sys
from collections import deque
sys.setrecursionlimit(10000)
L=open("/home/user/degree-diameter/research/squads/own-small/tools/bases/cubic/gh2.txt").read().split()
n,m=int(L[0]),int(L[1])
E=[(int(L[2+2*i]),int(L[3+2*i])) for i in range(m)]
adj=[set() for _ in range(n)]
for a,b in E: adj[a].add(b); adj[b].add(a)
# BFS order from 0 with parents
order=[0]; par={0:None}; dq=deque([0])
while dq:
    v=dq.popleft()
    for w in sorted(adj[v]):
        if w not in par: par[w]=v; order.append(w); dq.append(w)
def ordmul(p,q): return [p[q[i]] for i in range(n)]
def order_of(p):
    k=1; q=p[:]
    ident=list(range(n))
    while q!=ident:
        q=ordmul(p,q); k+=1
    return k
found={3:None,7:None}
count=0
img=[-1]*n; used=[False]*n
def dfs(i):
    global count
    if i==n:
        count+=1
        if count%1000==0: print("auts",count,file=sys.stderr)
        p=img[:]
        k=order_of(p)
        for o in (3,7):
            if k==o and found[o] is None: found[o]=p
        return all(found[o] is not None for o in (3,7))
    x=order[i]
    if i==0: cands=range(n)
    else: cands=adj[img[par[x]]]
    for c in cands:
        if used[c]: continue
        ok=True
        for w in adj[x]:
            if img[w]>=0 and img[w] not in adj[c]: ok=False; break
        if not ok: continue
        # for vertices mapped: neighbour-of-image must be neighbour
        img[x]=c; used[c]=True
        r=dfs(i+1)
        img[x]=-1; used[c]=False
        if r: return True
    return False
dfs(0)
for o in (3,7):
    print("order",o,"found" if found[o] else "none")
    if found[o]:
        open(f"sigma{o}.perm","w").write(" ".join(map(str,found[o]))+"\n")
print("auts seen",count)
