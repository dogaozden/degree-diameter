"""Z_5 x Z_k lift models of H(q) + 2 hops: hop k gets voltage (t_k, label), t = (1, 2) (polygon-cover part).
model  : sigma  | H(q) voltage
 p5k   : parallel (two disjoint 1-factors) | (0,0)
 p5kh  : parallel                           | (0, random)
 f5k   : random bijections                  | (0,0)
 f5kh  : random bijections                  | (0, random)
 t5k   : one 1-factor used twice (tripled flags) | (0,0)
"""
import random
import subprocess
import sys

import gh
from models import perfect_matching, SCR


def build(q, k, model, seed, H):
    rng = random.Random(seed)
    N = H.N
    holo = model.endswith('h')
    edges = [(p, L, 0, rng.randrange(k) if holo else 0) for (p, L) in gh.flags(H)]
    nbrs = [list(map(int, H.through[p])) for p in range(N)]
    if model.startswith('p'):
        s1 = perfect_matching(N, nbrs, rng)
        s2 = perfect_matching(N, nbrs, rng, forbid=s1)
    elif model.startswith('t'):
        s1 = perfect_matching(N, nbrs, rng)
        s2 = s1
    else:
        s1 = list(range(N)); rng.shuffle(s1)
        s2 = list(range(N)); rng.shuffle(s2)
    for p in range(N):
        edges.append((p, N + s1[p], 1, rng.randrange(k)))
        edges.append((p, N + s2[p], 2, rng.randrange(k)))
    return 2 * N, edges


if __name__ == '__main__':
    q = int(sys.argv[1]); model = sys.argv[2]; ks = [int(x) for x in sys.argv[3].split(',')]
    seeds = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    step = sys.argv[5] if len(sys.argv) > 5 else '1'
    H = gh.load(q)
    for k in ks:
        res = []
        for s in range(seeds):
            NB, edges = build(q, k, model, s, H)
            path = f'{SCR}/m5k_{model}_q{q}_k{k}_s{s}.txt'
            gh.write_base(path, NB, 5, k, edges)
            out = subprocess.run(['./liftdiam', path, '8', '4', step], capture_output=True, text=True).stdout
            res.append(int(out.split('unreached_pairs')[1].split()[0]))
        print(f'q={q} model={model} M=5x{k}={5*k} unreached={res}', flush=True)
