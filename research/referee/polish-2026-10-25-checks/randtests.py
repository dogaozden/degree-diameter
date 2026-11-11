import sys, itertools, random
sys.path.insert(0,'.')
from gf import diam, make
import thmA
from collections import deque
def bfs_diam_ok(n,edges):
    out=diam(n,edges); return int(out.split('diameter=')[1])
# ---------- Theorem B random tests on AS(3), AS(5)
for q in (3,5):
    F,pts,lines,on,w0,sums,e=thmA.build(q)
    s,t=q-1,q+1; nP=len(pts); nL=len(lines)
    rnd=random.Random(q)
    for trial in range(12):
        w=[rnd.choice([0,0,0,1,2]) for _ in range(nP)]
        M=[rnd.randrange(nL) for _ in range(rnd.randrange(0,40))]
        # vertex ids: old points 0..nP-1, clones, old lines, shadows
        cid={}; nxt=nP
        for p in range(nP):
            for i in range(1,w[p]+1): cid[(p,i)]=nxt; nxt+=1
        lid0=nxt; nxt+=nL
        edges=[]
        for j,L in enumerate(lines):
            for p in L:
                edges.append((p,lid0+j))
                for i in range(1,w[p]+1): edges.append((cid[(p,i)],lid0+j))
        stand={}
        for mu,j in enumerate(M):
            sh=nxt; nxt+=1
            for p in lines[j]:
                i=rnd.randrange(w[p]+1); v=p if i==0 else cid[(p,i)]
                edges.append((v,sh)); stand[v]=stand.get(v,0)+1
        n=nxt
        deg=[0]*n
        for a,b in edges: deg[a]+=1; deg[b]+=1
        # predicted max degree from table
        pred=max([s+1+sum(w[p] for p in L) for L in lines]+[t+1+stand.get(v,0) for v in range(nP)]+[t+1+stand.get(cid[k],0) for k in cid]+([s+1] if M else []))
        d=bfs_diam_ok(n,edges)
        assert d==4 and max(deg)==pred and n==nP+nL+sum(w)+len(M), (q,trial,d)
    print("Theorem B random stand-in tests passed on AS(%d)"%q)
# ---------- Corollary 1.4 random tests on PG(2,3) (n=3) and AS(3) (n=4)
def components_ok(elems,adj,A0,n):
    A0=set(A0); seen=set()
    for x in A0:
        if x in seen: continue
        comp=[];dq=deque([x]);seen.add(x)
        while dq:
            u=dq.popleft();comp.append(u)
            for y in adj[u]:
                if y in A0 and y not in seen: seen.add(y);dq.append(y)
        cs=set(comp); ne=sum(1 for u in comp for y in adj[u] if y in cs)//2
        if ne!=len(comp)-1: return False
        # diameter of tree
        def far(src):
            dist={src:0};dq=deque([src])
            while dq:
                u=dq.popleft()
                for y in adj[u]:
                    if y in cs and y not in dist: dist[y]=dist[u]+1;dq.append(y)
            m=max(dist,key=dist.get); return m,dist[m]
        a,_=far(comp[0]); _,dm=far(a)
        if dm>n-2: return False
    return True
def doubling(elems,adj,lev,m):
    ver={}
    for x in elems:
        for wd in itertools.product(range(m),repeat=lev.get(x,-1)+1): ver[(x,wd)]=len(ver)
    byx={}
    for (x,wd) in ver: byx.setdefault(x,[]).append(wd)
    comp=lambda a,b: a[:len(b)]==b if len(a)>=len(b) else b[:len(a)]==a
    E=set()
    for x in elems:
        for y in adj[x]:
            if x<y:
                for a in byx[x]:
                    for b in byx[y]:
                        if comp(a,b): E.add((ver[(x,a)],ver[(y,b)]))
    return len(ver),sorted(E)
def pg23():
    F=make(3)
    def norm(v):
        for i in range(2,-1,-1):
            if v[i]: iv=F.inv[v[i]]; return tuple(F.M[iv][x] for x in v)
    P=sorted(set(norm(v) for v in itertools.product(range(3),repeat=3) if any(v)))
    elems=[('p',p) for p in P]+[('l',L) for L in P]
    adj={x:[] for x in elems}
    for p in P:
        for L in P:
            if sum(a*b for a,b in zip(p,L))%3==0: adj[('p',p)].append(('l',L)); adj[('l',L)].append(('p',p))
    return elems,adj
def as3():
    F,pts,lines,on,w0,sums,e=thmA.build(3)
    elems=[('p',i) for i in range(len(pts))]+[('l',j) for j in range(len(lines))]
    adj={x:[] for x in elems}
    for j,L in enumerate(lines):
        for p in L: adj[('p',p)].append(('l',j)); adj[('l',j)].append(('p',p))
    return elems,adj
for name,(elems,adj),n in (("PG(2,3)",pg23(),3),("AS(3)",as3(),4)):
    rnd=random.Random(7); agree=0; tot=0; pos=0
    for trial in range(150):
        # grow A0 as random small trees/forests or random sets
        A0=set()
        for _ in range(rnd.randrange(1,4)):
            x=rnd.choice(elems); A0.add(x)
            for _ in range(rnd.randrange(0,4)):
                x=rnd.choice(adj[x]); A0.add(x)
        if rnd.random()<0.3: A0|=set(rnd.sample(elems,rnd.randrange(1,4)))
        A1=set(x for x in A0 if rnd.random()<0.3)
        lev={x:(1 if x in A1 else 0) for x in A0}
        pred=components_ok(elems,adj,A0,n)
        N,E=doubling(elems,adj,lev,2)
        d=bfs_diam_ok(N,[(a,b) for a,b in E])
        ok=(d<=n)
        tot+=1; agree+=(ok==pred); pos+=pred
    print(name,"Corollary 1.4 agreement",agree,"/",tot,"(trees-ok cases:",pos,")")
