"""Sanity checks: polygon covers of H(q) with random point->line matchings.
Z_{2j+1}, voltage 0 on H(q), t on matching t (t=1..j): diameter 7.  Z_10 with T={1,4}: diameter 8."""
import random
import subprocess
import sys

import gh

q = int(sys.argv[1])
seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
H = gh.load(q)
N = H.N
random.seed(seed)
base = [(p, L, 0, 0) for (p, L) in gh.flags(H)]


def matchings(T):
    out = []
    for t in T:
        perm = list(range(N))
        random.shuffle(perm)
        out += [(p, N + perm[p], t, 0) for p in range(N)]
    return out


for M, T, D in [(3, [1], 7), (5, [1, 2], 7), (10, [1, 4], 8), (11, [1, 4], 8)]:
    path = f'/tmp/claude-0/-home-user-degree-diameter/0ad899b8-ae47-58b5-b704-0795802a53c1/scratchpad/cov_q{q}_M{M}.txt'
    gh.write_base(path, 2 * N, M, 1, base + matchings(T))
    out = subprocess.run(['./liftdiam', path, str(D), '4'], capture_output=True, text=True).stdout
    print(f'q={q} M={M} T={T} D<={D}?', out.strip().replace('\n', ' | '))
