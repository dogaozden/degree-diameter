import random, sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/r2-d8/d1')
from vpe import *
for seed in range(1, 6):
    rng = random.Random(seed)
    N, flags = pg2_flags(3)
    V, adj = cover(N, flags, rng)
    D = len(adj[0])
    dX = bfs_stats(V, [(u, w) for u in range(V) for w in adj[u] if u < w], 99)[0]
    arcs = euler_arcs(V, adj, rng)
    out = []
    for sigma, ee in (('local', 'rand'), ('rand', 'rand'), ('local', 'succ1')):
        NY, E = build_Y(V, arcs, N, 5, D, rng, sigma=sigma, ee=ee)
        check_bip_deg(NY, E, V, arcs, N, 5)
        d, u5 = bfs_stats(NY, E, 5)
        out.append(f'{sigma}/{ee}: diam {d} (>5: {u5})')
    R = random_regular_bip(NY, D, rng)
    dR, uR = bfs_stats(NY, R, 5)
    print(f'seed {seed}: diam(X)={dX} | ' + ' | '.join(out) + f' | random: diam {dR} (>5: {uR})', flush=True)
