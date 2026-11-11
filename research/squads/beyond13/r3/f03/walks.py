# f03: nonbacktracking walks in a base graph -> net traversal vectors (universal abelian voltages)
import numpy as np, sys, time, json
def base_gp(n,k):
    edges=[]
    for i in range(n): edges.append((i,(i+1)%n))
    for i in range(n): edges.append((i,n+i))
    seen=set()
    for i in range(n):
        a,b=n+i,n+(i+k)%n
        key=(min(a,b),max(a,b))
        if key not in seen: seen.add(key); edges.append(key)
    return 2*n, edges
def base_k44():
    return 8, [(i,4+j) for i in range(4) for j in range(4)]
def base_k33():
    return 6, [(i,3+j) for i in range(3) for j in range(3)]
def base_cube():
    e=[]
    for v in range(8):
        for b in range(3):
            w=v^(1<<b)
            if v<w: e.append((v,w))
    return 8,e
def adjtables(V,edges):
    adj=[[] for _ in range(V)]
    for e,(a,b) in enumerate(edges):
        adj[a].append((b,e,1)); adj[b].append((a,e,-1))
    deg=len(adj[0]); assert all(len(x)==deg for x in adj)
    NB=np.array([[t[0] for t in adj[v]] for v in range(V)],dtype=np.int32)
    EB=np.array([[t[1] for t in adj[v]] for v in range(V)],dtype=np.int32)
    SB=np.array([[t[2] for t in adj[v]] for v in range(V)],dtype=np.int8)
    return NB,EB,SB
def walks(V,edges,src,D):
    """returns list per length L=0..D of (endpoint int32 array, X int8 [W,E] net traversal vectors)"""
    E=len(edges); NB,EB,SB=adjtables(V,edges)
    cur=np.array([src],dtype=np.int32); prev=np.array([-1],dtype=np.int32)
    X=np.zeros((1,E),dtype=np.int8)
    out=[(cur,X)]
    for L in range(1,D+1):
        nb=NB[cur]; mask=nb!=prev[:,None]
        rows,js=np.nonzero(mask)
        c0=cur[rows]
        newcur=nb[rows,js]; eidx=EB[c0,js]; sg=SB[c0,js]
        Xn=X[rows]
        Xn[np.arange(len(rows)),eidx]+=sg
        cur,prev,X=newcur,c0,Xn
        out.append((cur,X))
    return out
def distinct_counts(V,out,L):
    """distinct net vectors (hash) with length<=L, per endpoint; returns total distinct and per-endpoint array"""
    rng=np.random.default_rng(12345)
    r=rng.integers(1,2**62,size=out[0][1].shape[1],dtype=np.int64)|1
    ends=[];hs=[]
    for l in range(L+1):
        c,X=out[l]
        ends.append(c); hs.append(X.astype(np.int64)@r)
    c=np.concatenate(ends); h=np.concatenate(hs)
    key=np.unique(np.stack([h,c.astype(np.int64)],1),axis=0)
    per=np.bincount(key[:,1].astype(np.int64),minlength=V)
    return int(len(key)), per
if __name__=="__main__":
    which=sys.argv[1]; D=int(sys.argv[2])
    V,edges={'gp':lambda:base_gp(10,3),'k44':base_k44,'k33':base_k33,'cube':base_cube}[which]()
    t=time.time()
    out=walks(V,edges,0,D)
    tot=[sum(len(x[0]) for x in out[:l+1]) for l in range(D+1)]
    print(which,"V",V,"E",len(edges),"beta",len(edges)-V+1,"enum_time",round(time.time()-t,1))
    for L in range(1,D+1):
        d,per=distinct_counts(V,out,L)
        print(f"L<={L} walks={tot[L]} distinct={d} ratio={d/tot[L]:.4f} per_end_min={per.min()} max={per.max()}")
