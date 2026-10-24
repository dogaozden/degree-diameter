"""hexlib: load H(q) from hex/hex_q{q}.bin (research/p4/d6/hexgen.c format) and helpers for base multigraphs."""
import numpy as np, os, random

HERE = os.path.dirname(os.path.abspath(__file__))

def load_hex(q, path=None):
    """Return (n, lines) with lines an (n, q+1) int array of point ids; points and lines both 0..n-1."""
    path = path or os.path.join(HERE, '..', 'hex', f'hex_q{q}.bin')
    raw = np.fromfile(path, dtype=np.int32, count=3)
    q0, N, L = raw
    assert q0 == q and N == L
    lines = np.fromfile(path, dtype=np.int32, count=3 + L * (q + 1))[3:].reshape(L, q + 1)
    return int(N), lines

def point_lines(n, lines):
    q1 = lines.shape[1]
    pl = [[] for _ in range(n)]
    for l in range(n):
        for p in lines[l]:
            pl[p].append(l)
    return np.array(pl, dtype=np.int32)

def write_base(fn, n, edges, m, group='cyc', table=None):
    """edges: iterable of (p, l, g)."""
    with open(fn, 'w') as f:
        f.write(f"{n} {n} {m} {group}\n")
        if group == 'table':
            for row in table:
                f.write(' '.join(map(str, row)) + '\n')
        for p, l, g in edges:
            f.write(f"{p} {l} {g}\n")
