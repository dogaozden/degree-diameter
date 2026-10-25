import sys, collections, json
sys.path.insert(0,'/home/user/degree-diameter/research/squads/table-audit-r1/c7')
from load import load, props
def automorphisms(adj, limit=100000):
    n=len(adj); A=[set(a) for a in adj]
    # BFS order from 0 with parent
    order=[0]; par={0:None}; seen={0}; i=0
    while i<len(order):
        u=order[i]; i+=1
        for v in adj[u]:
            if v not in seen: seen.add(v); par[v]=u; order.append(v)
    idx={u:k for k,u in enumerate(order)}
    res=[]
    # candidate images for vertex 0: any vertex with same degree
    f=[-1]*n; used=[False]*n
    def rec(k):
        if len(res)>=limit: return
        if k==n:
            res.append(f[:]); return
        u=order[k]; p=par[u]
        if p is None: cands=[t for t in range(n) if len(adj[t])==len(adj[u]) and not used[t]]
        else: cands=[t for t in adj[f[p]] if not used[t]]
        mapped_nb=[w for w in adj[u] if f[w]>=0]
        for t in cands:
            if len(adj[t])!=len(adj[u]): continue
            ok=True
            for w in mapped_nb:
                if f[w] not in A[t]: ok=False; break
            if not ok: continue
            cnt=sum(1 for x in adj[t] if used[x])
            if cnt!=len(mapped_nb): continue
            f[u]=t; used[t]=True
            rec(k+1)
            f[u]=-1; used[t]=False
            if len(res)>=limit: return
    rec(0)
    return res
if __name__=="__main__":
    name=sys.argv[1]
    adj=load(name)
    import time; t=time.time()
    auts=automorphisms(adj)
    print(name,'|Aut found|=',len(auts),'time',round(time.time()-t,2))
    json.dump(auts, open(f'/home/user/degree-diameter/research/squads/table-audit-r1/c7/aut_{name}.json','w'))
