import sys, glob, os, re
from collections import deque
D = '/home/user/degree-diameter/research/squads/own-small/r1/b3/Sparse6'
def decode(line):
    s = line.strip()
    if s.startswith(':'): s = s[1:]
    data = [ord(c)-63 for c in s]
    if data[0] == 63:
        n = (data[1] << 12) | (data[2] << 6) | data[3]; pos = 4
    else:
        n = data[0]; pos = 1
    bits = []
    for d in data[pos:]:
        for j in range(5, -1, -1): bits.append((d >> j) & 1)
    k = 1
    while (1 << k) < n: k += 1
    adj = [set() for _ in range(n)]
    i = 0; v = 0
    while i + 1 + k <= len(bits):
        b = bits[i]; i += 1
        x = 0
        for j in range(k): x = (x << 1) | bits[i+j]
        i += k
        if b: v += 1
        if x > v: v = x
        else:
            if v < n and x < n and v != x:
                adj[v].add(x); adj[x].add(v)
    return n, adj
def diam(n, adj):
    best = 0
    for s in range(n):
        dist = [-1]*n; dist[s] = 0; q = deque([s])
        while q:
            u = q.popleft()
            for w in adj[u]:
                if dist[w] < 0: dist[w] = dist[u]+1; q.append(w)
        if min(dist) < 0: return 10**9
        best = max(best, max(dist))
    return best
def bip(n, adj):
    col = [-1]*n; col[0] = 0; q = deque([0])
    while q:
        u = q.popleft()
        for w in adj[u]:
            if col[w] < 0: col[w] = 1-col[u]; q.append(w)
            elif col[w] == col[u]: return None
    return col
if __name__ == '__main__':
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    for f in sorted(glob.glob(D+'/*.s6'), key=lambda p: (os.path.basename(p)[:3], int(re.findall(r'\d+', os.path.basename(p))[0]))):
        name = os.path.basename(f)
        n0 = int(re.findall(r'\d+', name)[0])
        if n0 < lo or n0 > hi: continue
        with open(f) as fh:
            for idx, line in enumerate(fh):
                if not line.strip(): continue
                n, adj = decode(line)
                if any(len(a) != 3 for a in adj): continue
                col = bip(n, adj)
                if col is None: continue
                d = diam(n, adj)
                # write base
                edges = sorted({(min(u,w), max(u,w)) for u in range(n) for w in adj[u]})
                out = f'/home/user/degree-diameter/research/squads/own-small/r1/b3/bases/{name[:-3]}_{idx}.txt'
                with open(out, 'w') as o:
                    o.write(f'{n} {len(edges)}\n')
                    for u, w in edges: o.write(f'{u} {w}\n')
                print(name, idx, 'n=%d' % n, 'diam=%d' % d, 'bip', flush=True)
