"""Cross-check gperm (permutation/group voltage BFS) against liftdiam on Z_10 lifts of H(5) + matchings T={1,4}."""
import random
import subprocess
import sys
import time

sys.path.insert(0, '/home/user/degree-diameter/research/squads/r1-d8/c8')
import gperm_lifts as GL  # noqa: E402
import gh  # noqa: E402

SCR = GL.SCR
q = 5
H = gh.load(q)
N = H.N
for seed in (7, 8):
    rng = random.Random(seed)
    hops = []
    for t in [1, 4]:
        perm = list(range(N)); rng.shuffle(perm)
        hops += [(p, N + perm[p], t) for p in range(N)]
    M = 10
    G = GL.Group(10, 1, 1)
    edges = [(p, Lv, G.rperm[0]) for (p, Lv) in gh.flags(H)] + [(u, v, G.rperm[t]) for (u, v, t) in hops]
    t0 = time.time()
    GL.write_perm_base(f'{SCR}/chk_z10_gp_{seed}.txt', 2 * N, M, edges)
    unr, out = GL.run_gperm(f'{SCR}/chk_z10_gp_{seed}.txt', 8, 1, 1)
    t1 = time.time() - t0
    print('gperm  ', out.strip().replace('\n', ' | '), f'[{t1:.1f}s]', flush=True)
    gh.write_base(f'{SCR}/chk_z10_ld_{seed}.txt', 2 * N, 10, 1,
                  [(u, v, t, 0) for (u, v, t) in hops] + [(p, Lv, 0, 0) for (p, Lv) in gh.flags(H)])
    o = subprocess.run(['/home/user/degree-diameter/research/theorems/d8/liftdiam', f'{SCR}/chk_z10_ld_{seed}.txt', '8', '1', '1'],
                       capture_output=True, text=True).stdout
    print('liftdiam', o.strip().replace('\n', ' | '), flush=True)
    # also D=7 to see the threshold
    unr7, _ = GL.run_gperm(f'{SCR}/chk_z10_gp_{seed}.txt', 7, 1, 1)
    print('gperm D=7 unreached', unr7, flush=True)
