"""c7 (wildcard): apartment-projection labels on hops.

Fix one apartment A (12-cycle of the incidence graph of H(q)) and project every vertex x to its unique nearest
vertex of A (gate property); owner[x] = position of that vertex on A, in 0..11.  Base = H(q) (zero voltage) plus two
hops (random non-incidence perfect matchings).  Lift group Z_5 x Z_k: hop i carries (t_i, w_i(p->L)) with the
polygon-cover part t = (1, 2), and w_i from the projection labels of the two endpoints.
Usage: apart_lift.py q k variant seed [D] [threads] [step]
"""
import os
import random
import subprocess
import sys
from collections import deque

sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d8')
import gh  # noqa: E402

OUT = '/home/user/degree-diameter/research/squads/r1-d8/c7'
LIFT = '/home/user/degree-diameter/research/theorems/d8/liftdiam'


def build_adj(H):
    N = H.N
    adj = [[] for _ in range(2 * N)]
    for k in range(N):
        for p in H.lines[k]:
            p = int(p)
            adj[p].append(N + k)
            adj[N + k].append(p)
    return adj


def apartment(H, adj):
    """12-cycle through point 0 and an opposite point: two internally disjoint geodesics of length 6."""
    N = H.N
    src = 0
    dist = [-1] * (2 * N)
    dist[src] = 0
    preds = [[] for _ in range(2 * N)]
    dq = deque([src])
    while dq:
        x = dq.popleft()
        for y in adj[x]:
            if dist[y] < 0:
                dist[y] = dist[x] + 1
                dq.append(y)
            if dist[y] == dist[x] + 1:
                preds[y].append(x)
    y0 = next(v for v in range(N) if dist[v] == 6)
    paths = []

    def dfs(v, path):
        if len(paths) >= 40:
            return
        if v == src:
            paths.append(path[::-1])
            return
        for u in preds[v]:
            dfs(u, path + [u])

    dfs(y0, [y0])
    p1 = paths[0]
    for p2 in paths[1:]:
        if not set(p1[1:-1]) & set(p2[1:-1]):
            return p1 + p2[-2:0:-1]
    raise RuntimeError('no disjoint geodesics')


def projection(adj, cyc):
    """owner[x] = index on cyc of the nearest vertex of the apartment (BFS from the apartment)."""
    owner = [-1] * len(adj)
    dq = deque()
    for i, v in enumerate(cyc):
        owner[v] = i
        dq.append(v)
    while dq:
        x = dq.popleft()
        for y in adj[x]:
            if owner[y] < 0:
                owner[y] = owner[x]
                dq.append(y)
    return owner


def hop_matching(N, H, rng):
    """random bijection points -> lines avoiding incidences"""
    inc = [set(int(L) for L in H.through[p]) for p in range(N)]
    s = list(range(N))
    rng.shuffle(s)
    for _ in range(100000):
        bad = [p for p in range(N) if s[p] in inc[p]]
        if not bad:
            break
        for p in bad:
            r = rng.randrange(N)
            s[p], s[r] = s[r], s[p]
    assert all(s[p] not in inc[p] for p in range(N))
    return s


def build(q, k, variant, seed, H, adj, owner, cyc):
    rng = random.Random(seed)
    N = H.N
    edges = []
    for p in range(N):
        for L in H.through[p]:
            edges.append((p, N + int(L), 0, 0))
    s1 = hop_matching(N, H, rng)
    s2 = hop_matching(N, H, rng)
    t = (1, 2)
    for hop, s in ((0, s1), (1, s2)):
        for p in range(N):
            L = s[p]
            w = label(variant, hop, owner, p, N + L, k)
            edges.append((p, N + L, t[hop], w))
    return 2 * N, edges


def label(variant, hop, owner, u, v, k):
    """voltage in Z_k on dart u -> v (u point, v vertex = N + line)"""
    if variant == 'rand':
        return 0  # replaced by caller randomness below
    op, ov = owner[u], owner[v]
    if variant == 'proj_pt':        # owner of the point only
        return (op + hop) % k
    if variant == 'proj_diff':      # difference of projections across the hop
        return (ov - op + hop) % k
    if variant == 'proj_sum':
        return (ov + op + hop) % k
    if variant == 'proj_half':      # position on A divided by 2 (point/line class collapsed)
        return ((op // 2) + hop * (ov // 2)) % k
    raise ValueError(variant)


def run(q, k, variant, seed, D=8, threads=1, step=1, tag=''):
    H = gh.load(q)
    adj = build_adj(H)
    cyc = apartment(H, adj)
    owner = projection(adj, cyc)
    rng = random.Random(seed)
    N = H.N
    if variant == 'rand':
        # random Z_k labels, same skeleton
        NB, edges = build(q, k, 'proj_pt', seed, H, adj, owner, cyc)
        edges = [(u, v, a, rng.randrange(k) if a else 0) for (u, v, a, b) in edges]
    else:
        NB, edges = build(q, k, variant, seed, H, adj, owner, cyc)
    path = f'{OUT}/base_{variant}_q{q}_k{k}_s{seed}{tag}.txt'
    gh.write_base(path, NB, 5, k, edges)
    out = subprocess.run([LIFT, path, str(D), str(threads), str(step)], capture_output=True, text=True).stdout
    unr = int(out.split('unreached_pairs')[1].split()[0])
    os.remove(path)
    return unr, out, cyc, owner


if __name__ == '__main__':
    q, k, variant, seed = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], int(sys.argv[4])
    step = int(sys.argv[5]) if len(sys.argv) > 5 else 1
    unr, out, cyc, owner = run(q, k, variant, seed, step=step)
    print(f'q={q} M={5*k} variant={variant} seed={seed} step={step} unreached={unr}', flush=True)
