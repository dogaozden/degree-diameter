import sys, os, collections
def decode(line):
    s = line.strip()
    assert s.startswith(':')
    data = [ord(c)-63 for c in s[1:]]
    # n
    i = 0
    if data[0] <= 62:
        n = data[0]; i = 1
    else:
        n = 0
        for k in range(1, 4): n = (n << 6) | data[k]
        i = 4
    # bits
    bits = []
    for v in data[i:]:
        for k in range(5, -1, -1): bits.append((v >> k) & 1)
    k = 1
    while (1 << k) < n: k += 1
    edges = []
    v = 0; p = 0
    def rd():
        nonlocal p
        x = 0
        for _ in range(k):
            x = (x << 1) | bits[p]; p += 1
        return x
    while p < len(bits):
        b = bits[p]; p += 1
        x = rd()
        if b: v += 1
        if x > v: v = x
        else: 
            if v < n: edges.append((x, v))
    # careful: standard algorithm
    return n, edges
def decode2(line):
    s = line.strip()[1:]
    data = [ord(c)-63 for c in s]
    if data[0] <= 62:
        n = data[0]; i = 1
    else:
        n = (data[1]<<12)|(data[2]<<6)|data[3]; i = 4
    bits = []
    for v in data[i:]:
        for k in range(5, -1, -1): bits.append((v >> k) & 1)
    k = 1
    while (1 << k) < n: k += 1
    edges = []
    v = 0; p = 0
    while p + 1 + k <= len(bits):
        b = bits[p]; p += 1
        x = 0
        for _ in range(k): x = (x << 1) | bits[p]; p += 1
        if b: v += 1
        if x > v: v = x
        elif v < n: edges.append((x, v))
    return n, edges
def bfs(adj, s):
    d = [-1]*len(adj); d[s]=0; q=collections.deque([s])
    while q:
        u=q.popleft()
        for w in adj[u]:
            if d[w]<0: d[w]=d[u]+1; q.append(w)
    return d
if __name__ == '__main__':
    out = []
    for f in sys.argv[1:]:
        for ln, line in enumerate(open(f)):
            n, E = decode2(line)
            adj = [[] for _ in range(n)]
            for a,b in E: adj[a].append(b); adj[b].append(a)
            deg = set(len(x) for x in adj)
            # bipartite
            col = [-1]*n; col[0]=0; bip=True; q=collections.deque([0])
            while q and bip:
                u=q.popleft()
                for w in adj[u]:
                    if col[w]<0: col[w]=1-col[u]; q.append(w)
                    elif col[w]==col[u]: bip=False
            diam = max(max(bfs(adj,s)) for s in range(n))
            girth = None
            print(os.path.basename(f), ln, n, len(E), sorted(deg), 'bip' if bip else 'nonbip', 'diam', diam, flush=True)
