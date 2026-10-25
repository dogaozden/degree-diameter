import sys, collections
SRC="/home/user/degree-diameter/research/projects/table-audit/lit/hafner_bipartite/"
def load(name):
    adj=[]
    for line in open(SRC+name):
        line=line.strip()
        if not line or line.startswith('#'): continue
        adj.append([int(x) for x in line.split()])
    return adj
def bfs(adj,s):
    n=len(adj); d=[-1]*n; d[s]=0; q=collections.deque([s])
    while q:
        u=q.popleft()
        for v in adj[u]:
            if d[v]<0: d[v]=d[u]+1; q.append(v)
    return d
def props(adj):
    n=len(adj)
    degs=collections.Counter(len(a) for a in adj)
    sym=all(u in adj[v] for u in range(n) for v in adj[u])
    # bipartite colouring
    col=[-1]*n; bip=True
    for s in range(n):
        if col[s]>=0: continue
        col[s]=0; q=collections.deque([s])
        while q:
            u=q.popleft()
            for v in adj[u]:
                if col[v]<0: col[v]=1-col[u]; q.append(v)
                elif col[v]==col[u]: bip=False
    diam=0; conn=True
    for s in range(n):
        d=bfs(adj,s)
        if min(d)<0: conn=False; break
        diam=max(diam,max(d))
    return dict(n=n,degs=dict(degs),sym=sym,bip=bip,conn=conn,diam=diam)
if __name__=="__main__":
    for name in sys.argv[1:]:
        a=load(name); print(name, props(a))
