import sys, glob, os, re
from collections import deque
def decode(line):
    s = line.strip()
    assert s.startswith(':')
    data = [ord(c)-63 for c in s[1:]]
    # n
    i = 0
    if data[0] <= 62: n = data[0]; i = 1
    else:
        n = 0
        for k in range(1,4): n = (n<<6) | data[k]
        i = 4
    bits = []
    for x in data[i:]:
        for k in range(5,-1,-1): bits.append((x>>k)&1)
    k = 1
    while (1<<k) < n: k += 1
    edges = []
    v = 0; p = 0
    def rd():
        nonlocal p
        val = 0
        for _ in range(k): val = (val<<1) | bits[p]; p += 1
        return val
    # sparse6 decoding
    v = 0
    while p < len(bits):
        b = bits[p]; p += 1
        if b: v += 1
        if p + k > len(bits) + 0 and p + k > len(bits): break
        x = rd()
        if x > v: v = x
        else: edges.append((x, v))
    return n, edges
def info(n, edges):
    adj = [[] for _ in range(n)]
    for a,b in edges: adj[a].append(b); adj[b].append(a)
    col = [-1]*n; col[0]=0; q=deque([0]); bip=True
    while q:
        u=q.popleft()
        for w in adj[u]:
            if col[w]<0: col[w]=1-col[u]; q.append(w)
            elif col[w]==col[u]: bip=False
    diam=0
    for s in range(n):
        dist=[-1]*n; dist[s]=0; q=deque([s])
        while q:
            u=q.popleft()
            for w in adj[u]:
                if dist[w]<0: dist[w]=dist[u]+1; q.append(w)
        diam=max(diam,max(dist))
    return bip, diam
out=[]
for f in sorted(glob.glob('/home/user/degree-diameter/research/squads/own-small/r1/b2/cens/Sparse6/*.s6')):
    nm=os.path.basename(f)[:-4]
    n=int(nm.split('_')[1])
    if n>64: continue
    for li,line in enumerate(open(f)):
        if not line.strip(): continue
        nn,E=decode(line)
        assert nn==n
        bip,diam=info(nn,E)
        if bip:
            out.append((nm,li,n,len(E),diam))
            tag=f"{nm}_{li}"
            with open(f"/home/user/degree-diameter/research/squads/own-small/r1/b2/work/{tag}.txt","w") as o:
                o.write(f"{n} {len(E)}\n")
                for a,b in sorted(E): o.write(f"{a} {b}\n")
for o in out: print(*o)
