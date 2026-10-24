"""V+E operation experiments (card d1).
X = Z_M polygon cover (M=5) of an incidence graph (points P, lines L) + two random point->line matchings with
voltages t=1,2; X is bipartite (P' = point copies, L' = line copies), D-regular, D even.
Eulerian orientation G of X (out = in = D/2). Owner rule: arc a=(u->w) is an edge-vertex owned by its tail u.
Y has vertices V(X) u A(G) (|V|+|E| vertices). Bipartition: A = P' u E_L (arcs with tail in L'),
B = L' u E_P (arcs with tail in P'). Edges of Y:
  owner:  u ~ arc (u->w)                       (D/2 per vertex)
  sigma:  P'-vertex x ~ arc e in E_P           (D/2 per x; sigma(e) != tail(e))
  tau:    L'-vertex y ~ arc f in E_L           (D/2 per y)
  E-E:    bipartite (D-2)-regular between E_P and E_L.
Degree D everywhere, bipartite, |Y| = |V| + |E|.
"""
import collections, itertools, random, subprocess, sys

sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d8')


def pg2_flags(q):
    """point-line flags of PG(2,q), q prime; returns (N, flags) with flags = (point, line) indices in 0..N-1"""
    pts = []
    for v in itertools.product(range(q), repeat=3):
        if any(v):
            i = next(j for j in range(3) if v[j])
            if v[i] == 1:
                pts.append(v)
    flags = [(a, b) for a, p in enumerate(pts) for b, w in enumerate(pts)
             if sum(x * y for x, y in zip(p, w)) % q == 0]
    return len(pts), flags


def hex_flags(q):
    import gh
    H = gh.load(q)
    N = H.N
    return N, [(p, k) for (p, L) in gh.flags(H) for k in [L - N]]


def cover(N, flags, rng, M=5, T=(1, 2)):
    """Z_M cover: vertex (x, i) -> x*M + i, x < N point, x >= N line (x-N). Flags voltage 0, matchings voltage t."""
    V = 2 * N * M
    adj = [[] for _ in range(V)]
    for p, l in flags:
        for i in range(M):
            a, b = p * M + i, (N + l) * M + i
            adj[a].append(b); adj[b].append(a)
    for t in T:
        perm = list(range(N)); rng.shuffle(perm)
        for p in range(N):
            for i in range(M):
                a, b = p * M + i, (N + perm[p]) * M + (i + t) % M
                adj[a].append(b); adj[b].append(a)
    assert all(len(set(x)) == len(x) for x in adj)
    return V, adj


def euler_arcs(V, adj, rng):
    edges = []; nb = [[] for _ in range(V)]
    for u in range(V):
        for w in adj[u]:
            if u < w:
                k = len(edges); edges.append((u, w))
                nb[u].append((w, k)); nb[w].append((u, k))
    for x in nb: rng.shuffle(x)
    ptr = [0] * V; used = [False] * len(edges); arcs = []
    for s in range(V):
        if ptr[s] >= len(nb[s]): continue
        stack = [s]; path = []
        while stack:
            v = stack[-1]
            while ptr[v] < len(nb[v]) and used[nb[v][ptr[v]][1]]: ptr[v] += 1
            if ptr[v] == len(nb[v]): path.append(stack.pop())
            else:
                w, k = nb[v][ptr[v]]; used[k] = True; stack.append(w)
        path.reverse(); arcs += list(zip(path, path[1:]))
    assert len(arcs) == len(edges)
    outd = [0] * V
    for a, b in arcs: outd[a] += 1
    assert set(outd) == {len(adj[0]) // 2}, set(outd)
    return arcs


def build_Y(V, arcs, N, M, D, rng, sigma='local', ee='succ1'):
    """sigma in {'local','rand'}; ee in {'succ1','rand'}"""
    isP = lambda v: (v // M) < N
    NY = V + len(arcs)
    E = [(a, V + k) for k, (a, b) in enumerate(arcs)]
    EP = [k for k, (a, b) in enumerate(arcs) if isP(a)]
    EL = [k for k, (a, b) in enumerate(arcs) if not isP(a)]
    half = D // 2
    # ---- sigma (P side) and tau (L side)
    for side_arcs, side_is_P in ((EP, True), (EL, False)):
        if sigma == 'local':
            # for each vertex y on the other side (the owner-side of the in-arcs): its in-arcs from this side
            # are matched bijectively to its out-neighbours on this side.
            inarcs = collections.defaultdict(list); outnb = collections.defaultdict(list)
            for k in side_arcs:
                a, b = arcs[k]
                inarcs[b].append(k)          # arc a->b with a on this side, b on other side
            for k in side_arcs:
                a, b = arcs[k]
                outnb[b].append(a)           # placeholder, recomputed below
            # out-arcs of a middle vertex y (other side): arcs y->x with x on this side
            mid = collections.defaultdict(list)
            for k, (a, b) in enumerate(arcs):
                if (isP(a) != side_is_P):
                    mid[a].append(b)         # a: middle vertex, b: vertex on this side
            for y, ins in inarcs.items():
                targets = mid[y][:]
                rng.shuffle(targets)
                assert len(targets) == len(ins)
                for k, x in zip(ins, targets):
                    E.append((x, V + k))
        else:
            pool = [x for x in range(V) if isP(x) == side_is_P for _ in range(half)]
            rng.shuffle(pool)
            owner = {k: arcs[k][0] for k in side_arcs}
            # repair conflicts sigma(e) == owner(e)
            for _ in range(10000):
                bad = [i for i, k in enumerate(side_arcs) if pool[i] == owner[k]]
                if not bad: break
                i = rng.choice(bad); j = rng.randrange(len(pool)); pool[i], pool[j] = pool[j], pool[i]
            assert all(pool[i] != owner[k] for i, k in enumerate(side_arcs))
            for x, k in zip(pool, side_arcs):
                E.append((x, V + k))
    # ---- E-E edges between EP and EL
    have = set()
    if ee == 'succ1':
        for e in EP:
            l = arcs[e][1]
            for f in EL:
                if arcs[f][0] == l:
                    have.add((e, f))
        # sanity: 3 per vertex
        cnt = collections.Counter(e for e, f in have)
        assert all(cnt[e] == half for e in EP)
        matchings_needed = D - 2 - half
    else:
        matchings_needed = D - 2
    for _ in range(matchings_needed):
        for _try in range(10000):
            perm = EL[:]; rng.shuffle(perm)
            pairs = list(zip(EP, perm))
            if all(pr not in have for pr in pairs):
                break
        have.update(pairs)
    for e, f in have:
        E.append((V + e, V + f))
    return NY, E


def check_bip_deg(NY, E, V, arcs, N, M):
    isP = lambda v: (v // M) < N
    side = [0] * NY
    for v in range(V): side[v] = 0 if isP(v) else 1
    for k, (a, b) in enumerate(arcs): side[V + k] = 1 if isP(a) else 0
    deg = [0] * NY; seen = set()
    for u, v in E:
        assert side[u] != side[v], ('not bipartite', u, v)
        key = (min(u, v), max(u, v)); assert key not in seen, 'multi-edge'; seen.add(key)
        deg[u] += 1; deg[v] += 1
    return collections.Counter(deg)


def bfs_stats(n, E, target):
    adj = [[] for _ in range(n)]
    for u, v in E: adj[u].append(v); adj[v].append(u)
    diam = 0; unreached = 0; total = 0
    for s in range(n):
        dist = [-1] * n; dist[s] = 0; dq = collections.deque([s])
        while dq:
            x = dq.popleft()
            for y in adj[x]:
                if dist[y] < 0:
                    dist[y] = dist[x] + 1; dq.append(y)
        m = max(dist)
        if min(dist) < 0: m = 10**9
        diam = max(diam, m)
        unreached += sum(1 for d in dist if d > target)
    return diam, unreached // 2


def random_regular_bip(n, D, rng):
    """random D-regular bipartite graph on n vertices (n/2 + n/2), union of D random matchings (simple)"""
    h = n // 2
    while True:
        E = set(); ok = True
        for _ in range(D):
            for _try in range(1000):
                perm = list(range(h)); rng.shuffle(perm)
                pairs = [(i, h + perm[i]) for i in range(h)]
                if not any(p in E for p in pairs): break
            else:
                ok = False; break
            E.update(pairs)
        if ok: return sorted(E)
