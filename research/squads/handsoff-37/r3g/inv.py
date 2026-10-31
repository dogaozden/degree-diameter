import sys, collections, hashlib

def load(fn):
    with open(fn) as f:
        n = int(f.readline())
        adj = [[] for _ in range(n)]
        for line in f:
            p = line.split()
            if len(p) < 2:
                continue
            a, b = int(p[0]), int(p[1])
            adj[a].append(b)
            adj[b].append(a)
    return n, adj

def inv(fn):
    n, adj = load(fn)
    prof = []
    for s in range(n):
        dist = [-1] * n
        dist[s] = 0
        q = collections.deque([s])
        cnt = collections.Counter()
        while q:
            x = q.popleft()
            cnt[dist[x]] += 1
            for y in adj[x]:
                if dist[y] < 0:
                    dist[y] = dist[x] + 1
                    q.append(y)
        prof.append(tuple(cnt[d] for d in range(9)))
    c = collections.Counter(prof)
    sig = tuple(sorted(c.items()))
    return hashlib.md5(repr(sig).encode()).hexdigest()[:10], len(c), sorted(c.values())[-3:]

for fn in sys.argv[1:]:
    h, nd, top = inv(fn)
    print(fn.split('/')[-1], 'profile-class-hash', h, 'distinct vertex profiles', nd, 'largest classes', top)
