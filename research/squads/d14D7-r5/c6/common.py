"""Shared helpers for card c6 (q = 11, Q = x0x4 + x1x5 + x2x6 - x3^2, B(x,y) as in the brief)."""
import os, sys
import numpy as np

Q = 11
OVOID = '/home/user/degree-diameter/research/cell147/ovoid'
sys.path.insert(0, OVOID)
import ovlib as L  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
R756_PATH = '/home/user/degree-diameter/research/d13D7/sets/R756_r4c1_coords.txt'
G15_PATH = os.path.join(OVOID, 'g15.txt')
INV = np.array([0] + [pow(i, Q - 2, Q) for i in range(1, Q)], dtype=np.int64)


def normalize_rows(X):
    """projective normal form: first nonzero coordinate equal to 1 (rows must be nonzero)."""
    X = np.asarray(X, dtype=np.int64) % Q
    first = np.argmax(X != 0, axis=1)
    lead = X[np.arange(len(X)), first]
    assert np.all(lead != 0)
    return X * INV[lead][:, None] % Q


def load_points(path):
    X = np.loadtxt(path, dtype=np.int64, comments='#', ndmin=2)
    return normalize_rows(X)


def key_set(X):
    return {tuple(int(v) for v in r) for r in X}


def gram_B(x, y):
    """B(x,y) = x0y4+x4y0+x1y5+x5y1+x2y6+x6y2-2x3y3 (mod 11) for row arrays x (n,7), y (m,7)."""
    x = np.asarray(x, dtype=np.int64); y = np.asarray(y, dtype=np.int64)
    Y = y[:, [4, 5, 6, 3, 0, 1, 2]].copy()
    Y[:, 3] = (-2 * Y[:, 3]) % Q
    return (x @ Y.T) % Q


def all_singular_points():
    """all projective points of Q(6,11) as normalized rows (177156 of them)."""
    tot = Q ** 7
    c = np.arange(tot, dtype=np.int64)
    V = np.stack([(c // Q ** i) % Q for i in range(7)], axis=1)
    nz = V != 0
    first = np.argmax(nz, axis=1)
    keep = nz.any(axis=1)
    lead = V[np.arange(tot), first]
    keep &= lead == 1
    V = V[keep]
    s = (V[:, 0] * V[:, 4] + V[:, 1] * V[:, 5] + V[:, 2] * V[:, 6] - V[:, 3] ** 2) % Q
    return V[s == 0]


def apply_mat(M, X):
    """apply 7x7 matrix M to the row vectors X (acting on column vectors), return projectively normalized rows."""
    M = np.asarray(M, dtype=np.int64) % Q
    Y = (np.asarray(X, dtype=np.int64) @ M.T) % Q
    return normalize_rows(Y)


def stabilizes(M, R):
    """True if M maps the projective point set R (normalized rows) onto itself."""
    img = apply_mat(M, R)
    return key_set(img) == key_set(R)


def write_points(path, X, comment):
    with open(path, 'w') as f:
        f.write(f'# {len(X)} pairwise non-orthogonal points of Q(6,11); {comment}\n')
        for r in X:
            f.write(' '.join(str(int(v)) for v in r) + '\n')


def mat_str(M):
    return '\n'.join(' '.join(str(int(x) % Q) for x in r) for r in M)
