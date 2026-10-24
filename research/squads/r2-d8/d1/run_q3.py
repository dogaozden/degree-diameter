import random, sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/r2-d8/d1')
from vpe import *
rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
N, flags = pg2_flags(3)
V, adj = cover(N, flags, rng)
D = len(adj[0])
print('X: vertices', V, 'degree', set(len(x) for x in adj), 'diam(X)', bfs_stats(V, [(u, w) for u in range(V) for w in adj[u] if u < w], 99)[0])
arcs = euler_arcs(V, adj, rng)
for sigma in ('local', 'rand'):
    for ee in ('succ1', 'rand'):
        try:
            NY, E = build_Y(V, arcs, N, 5, D, rng, sigma=sigma, ee=ee)
            degs = check_bip_deg(NY, E, V, arcs, N, 5)
            diam, unr = bfs_stats(NY, E, 5)
            print(f'sigma={sigma:5s} ee={ee:5s} |Y|={NY} degs={dict(degs)} diam(Y)={diam} pairs>5: {unr}')
        except AssertionError as ex:
            print('fail', sigma, ee, ex)
for trial in range(2):
    E = random_regular_bip(NY, D, rng)
    print('random 6-regular bipartite on', NY, 'vertices: diam', bfs_stats(NY, E, 5)[0], 'pairs>5', bfs_stats(NY, E, 5)[1])
