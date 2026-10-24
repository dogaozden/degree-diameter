"""c5: colour voltages on the flags of H(q), cyclic group Z_M (M1 = M, M2 = 1), constant hop voltages w1, w2.

Base B = H(q) + two random point->line bijections s1, s2 (the hops).  The flags are properly edge-coloured with
q+1 colours by repeated random perfect matchings; colour c gets voltage v[c] on the dart point->line.
Scorer: research/theorems/d8/liftdiam (stdin input, THREADS=1).
"""
import os
import random
import subprocess
import sys

D8 = '/home/user/degree-diameter/research/theorems/d8'
LIFTDIAM = os.path.join(D8, 'liftdiam')
sys.path.insert(0, D8)
import gh  # noqa: E402
from models import perfect_matching  # noqa: E402

Q = 5
H = gh.load(Q)
N = H.N
THROUGH = [list(map(int, H.through[p])) for p in range(N)]


def colouring(seed):
    """q+1 perfect matchings points->lines partitioning all flags (each step removes one matching)."""
    rng = random.Random(seed)
    rem = [list(t) for t in THROUGH]
    classes = []
    for _ in range(Q + 1):
        m = perfect_matching(N, rem, rng)
        classes.append(m)
        for p in range(N):
            rem[p].remove(m[p])
    assert all(not rem[p] for p in range(N))
    return classes


def hops(seed):
    rng = random.Random(seed)
    s1 = list(range(N)); rng.shuffle(s1)
    s2 = list(range(N)); rng.shuffle(s2)
    return s1, s2


def base_text(M, classes, v, w, s1, s2, perm=None):
    """liftdiam text; perm (vertex relabelling, a permutation of 0..2N-1) randomises which sources a stride samples."""
    lines = []
    P = perm if perm is not None else range(2 * N)
    for c in range(Q + 1):
        m = classes[c]
        for p in range(N):
            lines.append(f'{P[p]} {P[N + m[p]]} {v[c] % M} 0')
    for p in range(N):
        lines.append(f'{P[p]} {P[N + s1[p]]} {w[0] % M} 0')
        lines.append(f'{P[p]} {P[N + s2[p]]} {w[1] % M} 0')
    head = f'{2 * N} {M} 1 {len(lines)}\n'
    return head + '\n'.join(lines) + '\n'


def unreached(text, step=1, D=8):
    out = subprocess.run(['timeout', '900', 'nice', '-n', '10', LIFTDIAM, '-', str(D), '1', str(step)],
                         input=text, capture_output=True, text=True).stdout
    return int(out.split('unreached_pairs')[1].split()[0])


def check_colouring(classes):
    seen = set()
    for m in classes:
        assert sorted(m) == list(range(N)) or len(set(m)) == N
        for p in range(N):
            seen.add((p, m[p]))
    assert len(seen) == (Q + 1) * N
    flags = {(p, L) for p in range(N) for L in THROUGH[p]}
    assert seen == flags


if __name__ == '__main__':
    import time
    classes = colouring(1)
    check_colouring(classes)
    print('colouring ok', flush=True)
    s1, s2 = hops(1)
    rng = random.Random(5)
    for M in (20, 25):
        v = [0] + [rng.randrange(M) for _ in range(Q)]
        w = [rng.randrange(M), rng.randrange(M)]
        text = base_text(M, classes, v, w, s1, s2)
        for step in (8, 4):
            t0 = time.time()
            u = unreached(text, step)
            print(f'M={M} step={step} unreached={u} time={time.time() - t0:.2f}s', flush=True)
