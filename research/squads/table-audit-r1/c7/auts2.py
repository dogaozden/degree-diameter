import sys, collections, json, time
sys.path.insert(0,'/home/user/degree-diameter/research/squads/table-audit-r1/c7')
import numpy as np
from load import load
def apsp(adj):
    n=len(adj); D=np.full((n,n),-1,dtype=np.int32)
    for s in range(n):
        d=[-1]*n; d[s]=0; q=collections.deque([s])
        while q:
            u=q.popleft()
            for v in adj[u]:
                if d[v]<0: d[v]=d[u]+1; q.append(v)
        D[s]=d
    return D
def automorphisms(adj, D, limit=100000, timeout=600):
    n=len(adj); t0=time.time()
    order=[0]; par={0:None}; seen={0}; i=0
    while i<len(order):
        u=order[i]; i+=1
        for v in adj[u]:
            if v not in seen: seen.add(v); par[v]=u; order.append(v)
    res=[]; f=[-1]*n; used=[False]*n
    sig=[tuple(sorted(D[v].tolist())) for v in range(n)]
    def rec(k):
        if len(res)>=limit or time.time()-t0>timeout: return
        if k==n: res.append(f[:]); return
        u=order[k]; p=par[u]
        if p is None: cands=[t for t in range(n) if sig[t]==sig[u]]
        else: cands=[t for t in adj[f[p]] if not used[t]]
        done=order[:k]
        Du=D[u]
        for t in cands:
            if used[t] or sig[t]!=sig[u]: continue
            ok=True
            Dt=D[t]
            for w in done:
                if Dt[f[w]]!=Du[w]: ok=False; break
            if not ok: continue
            f[u]=t; used[t]=True
            rec(k+1)
            f[u]=-1; used[t]=False
            if len(res)>=limit or time.time()-t0>timeout: return
    rec(0)
    return res
if __name__=="__main__":
    name=sys.argv[1]; limit=int(sys.argv[2]) if len(sys.argv)>2 else 100000
    adj=load(name)
    t=time.time(); D=apsp(adj); print('apsp',round(time.time()-t,2),flush=True)
    t=time.time()
    auts=automorphisms(adj,D,limit=limit)
    print(name,'|Aut found|=',len(auts),'time',round(time.time()-t,2),flush=True)
    json.dump(auts, open(f'/home/user/degree-diameter/research/squads/table-audit-r1/c7/aut_{name}.json','w'))
