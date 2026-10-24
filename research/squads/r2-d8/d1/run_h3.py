import random, subprocess, sys, time
sys.path.insert(0, '/home/user/degree-diameter/research/squads/r2-d8/d1')
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d8')
from vpe import *
import gh
q = int(sys.argv[1]); seed = int(sys.argv[2]); D_target = int(sys.argv[3]) if len(sys.argv) > 3 else 8
rng = random.Random(seed)
N, flags = hex_flags(q)
V, adj = cover(N, flags, rng)
D = len(adj[0])
LIFT = '/home/user/degree-diameter/research/theorems/d8/liftdiam'
SCR = '/home/user/degree-diameter/research/squads/r2-d8/d1'
def run(path, n, E, D_, tag):
    gh.write_base(path, n, 1, 1, [(u, v, 0, 0) for u, v in E])
    t = time.time()
    out = subprocess.run(['timeout', '900', 'nice', '-n', '10', LIFT, path, str(D_), '1'], capture_output=True, text=True).stdout
    print(f'{tag}: D<={D_}', out.strip().replace('\n', ' | '), f'({time.time()-t:.1f}s)', flush=True)
    return out
Xedges = [(u, w) for u in range(V) for w in adj[u] if u < w]
run(f'{SCR}/X_q{q}_s{seed}.txt', V, Xedges, D_target - 1, f'X(q={q}) cover+2 matchings, |V|={V} deg {D}')
arcs = euler_arcs(V, adj, rng)
for sigma, ee in (('local', 'rand'), ('rand', 'rand')):
    NY, E = build_Y(V, arcs, N, 5, D, rng, sigma=sigma, ee=ee)
    degs = check_bip_deg(NY, E, V, arcs, N, 5)
    run(f'{SCR}/Y_q{q}_s{seed}_{sigma}_{ee}.txt', NY, E, D_target, f'V+E sigma={sigma} ee={ee} |Y|={NY} degs={dict(degs)}')
E = random_regular_bip(NY, D, rng)
run(f'{SCR}/R_q{q}_s{seed}.txt', NY, E, D_target, f'random {D}-regular bipartite |n|={NY}')
