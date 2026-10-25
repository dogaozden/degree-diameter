"""c6 helpers: H(q) + one hop matching, cyclic lifts. Uses research/theorems/d8/gh.py (read-only)."""
import os, random, subprocess, sys
D8 = '/home/user/degree-diameter/research/theorems/d8'
sys.path.insert(0, D8)
import gh  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))


def load(q):
    return gh.load(q)


def collinear_lists(H):
    """X[x] = points collinear with x, including x (closed collinearity neighbourhood, size 1+q(q+1))"""
    N = H.N
    X = []
    for x in range(N):
        s = {x}
        for L in H.through[x]:
            for p in H.lines[int(L)]:
                s.add(int(p))
        X.append(sorted(s))
    return X


def write_base(path, H, M, t, s, Mz=None):
    """cyclic Z_M lift: H-flags voltage 0, hop p -> N+s[p] voltage t[p] (ints mod M)."""
    N = H.N
    edges = [(p, L, 0, 0) for (p, L) in gh.flags(H)]
    edges += [(p, N + s[p], t[p] % M, 0) for p in range(N)]
    gh.write_base(path, 2 * N, M, 1, edges)
    return path


def liftdiam(path, D=8, step=1):
    out = subprocess.run([os.path.join(HERE, 'liftdiam'), path, str(D), '1', str(step)],
                         capture_output=True, text=True).stdout
    unr = int(out.split('unreached_pairs')[1].split()[0])
    ecc = out.split('max_ecc')[1].split()[0]
    return unr, ecc, out
