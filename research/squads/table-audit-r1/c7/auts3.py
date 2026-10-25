import sys, json, time
sys.path.insert(0,'/home/user/degree-diameter/research/squads/table-audit-r1/c7')
import numpy as np
from load import load
from auts2 import apsp
# Automorphisms by backtracking with dynamic ordering: next vertex = unmapped vertex with most
# mapped neighbours; candidates = common neighbourhood of their images; distances checked.
def automorphisms(adj, D, limit=100000, timeout=100, root_cands=None):
    n=len(adj); t0=time.time()
    sig=[tuple(sorted(D[v].tolist())) for v in range(n)]
    res=[]; f=[-1]*n; used=[False]*n; mapped=[]
    cnt=[0]*n  # mapped-neighbour count for unmapped vertices
    def rec():
        if len(res)>=limit or time.time()-t0>timeout: return
        if len(mapped)==n: res.append(f[:]); return
        # choose next vertex
        best=-1; bc=0
        for u in range(n):
            if f[u]<0 and cnt[u]>bc: bc=cnt[u]; best=u
        if best<0:
            # no mapped neighbours (only at root): choose any unmapped
            best=next(u for u in range(n) if f[u]<0)
        u=best
        mnb=[w for w in adj[u] if f[w]>=0]
        if mnb:
            cs=set(adj[f[mnb[0]]])
            for w in mnb[1:]: cs &= set(adj[f[w]])
            cands=[t for t in cs if not used[t]]
        else:
            cands=root_cands if (not mapped and root_cands is not None) else [t for t in range(n) if not used[t]]
        Du=D[u]
        for t in cands:
            if used[t] or sig[t]!=sig[u]: continue
            if mapped:
                idx=np.array(mapped)
                img=np.array([f[w] for w in mapped])
                if not np.array_equal(D[t][img], Du[idx]): continue
            f[u]=t; used[t]=True; mapped.append(u)
            for w in adj[u]: cnt[w]+=1
            rec()
            for w in adj[u]: cnt[w]-=1
            mapped.pop(); f[u]=-1; used[t]=False
            if len(res)>=limit or time.time()-t0>timeout: return
    rec()
    return res
if __name__=="__main__":
    name=sys.argv[1]; limit=int(sys.argv[2]) if len(sys.argv)>2 else 100000
    adj=load(name)
    D=apsp(adj)
    t=time.time()
    auts=automorphisms(adj,D,limit=limit,timeout=150)
    print(name,'|Aut found|=',len(auts),'time',round(time.time()-t,2),flush=True)
    json.dump(auts, open(f'/home/user/degree-diameter/research/squads/table-audit-r1/c7/aut_{name}.json','w'))
