"""Random lift models of H(q) + two extra point-line edges per vertex, voltages in Z_M (zero on H(q) unless said).

model 'free'   : sigma_1, sigma_2 random bijections points->lines, labels random in Z_M
model 'par2'   : sigma_1, sigma_2 two disjoint 1-factors of the incidence graph (parallel hops), labels random
model 'par1'   : sigma_1 = sigma_2 = one 1-factor (each sigma-flag tripled), labels random
model 'poly'   : polygon-cover voltages t1, t2 on random bijections (constant labels)
model 'holo'   : 'free' plus random voltages on the H(q) flags
"""
import random
import subprocess
import sys

import gh

SCR = '/tmp/claude-0/-home-user-degree-diameter/0ad899b8-ae47-58b5-b704-0795802a53c1/scratchpad'


def perfect_matching(N, nbrs, rng, forbid=None):
    """random perfect matching point->line in the bipartite graph nbrs[p] (list of line ids 0..N-1)"""
    order = list(range(N))
    rng.shuffle(order)
    nb = [list(x) for x in nbrs]
    for x in nb:
        rng.shuffle(x)
    if forbid is not None:
        nb = [[L for L in nb[p] if L != forbid[p]] for p in range(N)]
    matchL = [-1] * N
    matchP = [-1] * N
    # Hopcroft-Karp style: repeated BFS/DFS augment
    import collections
    while True:
        dist = {}
        dq = collections.deque()
        for p in range(N):
            if matchP[p] < 0:
                dist[p] = 0
                dq.append(p)
        found = False
        while dq:
            p = dq.popleft()
            for L in nb[p]:
                p2 = matchL[L]
                if p2 < 0:
                    found = True
                elif p2 not in dist:
                    dist[p2] = dist[p] + 1
                    dq.append(p2)
        if not found:
            break

        def dfs(p):
            for L in nb[p]:
                p2 = matchL[L]
                if p2 < 0 or (dist.get(p2, -1) == dist[p] + 1 and dfs(p2)):
                    matchP[p] = L
                    matchL[L] = p
                    return True
            dist[p] = -1
            return False
        sys.setrecursionlimit(100000)
        for p in order:
            if matchP[p] < 0:
                dfs(p)
    assert all(m >= 0 for m in matchP), 'no perfect matching'
    return matchP


def build(q, M, model, seed, H=None):
    rng = random.Random(seed)
    H = H or gh.load(q)
    N = H.N
    edges = []
    holo = model == 'holo'
    for (p, L) in gh.flags(H):
        edges.append((p, L, rng.randrange(M) if holo else 0, 0))
    nbrs = [list(map(int, H.through[p])) for p in range(N)]
    if model in ('free', 'holo', 'poly'):
        s1 = list(range(N)); rng.shuffle(s1)
        s2 = list(range(N)); rng.shuffle(s2)
    elif model == 'par2':
        s1 = perfect_matching(N, nbrs, rng)
        s2 = perfect_matching(N, nbrs, rng, forbid=s1)
    elif model == 'par1':
        s1 = perfect_matching(N, nbrs, rng)
        s2 = s1
    for p in range(N):
        if model == 'poly':
            a, b = 1, 4 if M >= 10 else 2
        else:
            a, b = rng.randrange(1, M), rng.randrange(1, M)
            if model == 'par1':
                while b == a:
                    b = rng.randrange(1, M)
        edges.append((p, N + s1[p], a, 0))
        edges.append((p, N + s2[p], b, 0))
    return 2 * N, edges


def test(q, M, model, seed, D=8, threads=4, step=1, H=None):
    NB, edges = build(q, M, model, seed, H)
    path = f'{SCR}/m_{model}_q{q}_M{M}_s{seed}.txt'
    gh.write_base(path, NB, M, 1, edges)
    out = subprocess.run(['./liftdiam', path, str(D), str(threads), str(step)], capture_output=True, text=True).stdout
    unr = int(out.split('unreached_pairs')[1].split()[0])
    return unr, out


if __name__ == '__main__':
    q = int(sys.argv[1]); model = sys.argv[2]; Ms = [int(x) for x in sys.argv[3].split(',')]
    seeds = int(sys.argv[4]) if len(sys.argv) > 4 else 2
    step = int(sys.argv[5]) if len(sys.argv) > 5 else 1
    H = gh.load(q)
    for M in Ms:
        res = [test(q, M, model, s, step=step, H=H)[0] for s in range(seeds)]
        print(f'q={q} model={model} M={M} unreached={res}', flush=True)
