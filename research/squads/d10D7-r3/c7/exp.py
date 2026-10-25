import sys, subprocess, os
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gen import *
HERE = os.path.dirname(os.path.abspath(__file__))
VIOL = os.path.join(HERE, 'viol')

def check(n, edges, tag):
    fn = os.path.join(HERE, 'tmp_%s.edges' % tag)
    write(n, edges, fn)
    out = subprocess.run(['nice', '-n', '10', VIOL, fn, '7'], capture_output=True, text=True, timeout=1500).stdout.strip()
    os.remove(fn)
    return out

if __name__ == '__main__':
    exp, seed = sys.argv[1], int(sys.argv[2])
    q = 5
    N, LP = load_hex(q)
    rng = np.random.default_rng(seed)
    M = rng.permutation(N)
    if exp == 'base':
        n, E = build(N, LP, M, [], [], 0)
    elif exp == 'hub1':   # one freed pair, 3 deleted edges, 2 hubs, no hub link
        p = int(rng.integers(N)); l = int(M[p])
        dl = [(p, i) for i in range(3)]
        Z, Zp = 6 * N, 6 * N + 1
        new = [(Z, i * 2 * N + p) for i in range(3)] + [(Zp, i * 2 * N + N + l) for i in range(3)]
        if len(sys.argv) > 3 and sys.argv[3] == 'link': new.append((Z, Zp))
        n, E = build(N, LP, M, dl, new, 2)
    elif exp == 'cl8':   # 4 deleted extra edges, 8 vertices: K8 minus matching, one attachment per freed endpoint
        ps = rng.choice(N * 3, 4, replace=False)
        dl = [(int(x) % N, int(x) // N) for x in ps]
        ends = []
        for (p, i) in dl:
            ends.append(i * 2 * N + p); ends.append(((i + 1) % 3) * 2 * N + N + int(M[p]))
        match = {(0, 2), (1, 4), (3, 6), (5, 7)}
        new = []
        for j in range(8):
            new.append((6 * N + j, ends[j]))
            for k in range(j + 1, 8):
                if (j, k) not in match: new.append((6 * N + j, 6 * N + k))
        n, E = build(N, LP, M, dl, new, 8)
    elif exp == 'path2':   # 1 deleted extra edge, 2 vertices subdividing it (path a-w0-w1-b)
        p = int(rng.integers(N)); i = int(rng.integers(3))
        a = i * 2 * N + p; b = ((i + 1) % 3) * 2 * N + N + int(M[p])
        new = [(a, 6 * N), (6 * N, 6 * N + 1), (6 * N + 1, b)]
        n, E = build(N, LP, M, [(p, i)], new, 2)
    else:
        raise SystemExit('unknown exp')
    print(exp, 'seed', seed, 'extra vertices', n - 6 * N + 6 * N - 6 * N, check(n, E, exp + str(seed)))
