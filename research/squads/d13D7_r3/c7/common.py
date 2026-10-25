"""Shared helpers for card c7 (round 3): fibration + points at infinity, reduced to a covering count.
Coset space: v = (s,b,c,f) in F_11^4 (coset of u=(1,0,0,9,0) in the affine chart; rep (a,b,c,e,f)=(0,b,c,s,f)).
Points at infinity compatible with all lines are x=(0,x1,x2,x3,x4,2*x1,x6) (x5 = 2 x1 forced); their direction
n=(x1,x6,-2*x3,x2) lies on the elliptic quadric E: 8 n_s^2 + 4 n_b n_f - n_c^2 = 0 (122 projective directions), and
x is blocked by coset v iff n.v + x4 = 0.  Two such points are opposite iff their directions differ."""
import numpy as np, os, itertools
Q = 11
HEX = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'd13D7', 'hex', 'hex_q11.bin')
HEX = os.path.abspath(HEX)
INV2 = 6  # 2^{-1} mod 11

def load_hex(path=HEX):
    raw = open(path, 'rb').read()
    q, N, L = np.frombuffer(raw[:12], dtype=np.int32)
    coord = np.frombuffer(raw[12 + 4 * L * (q + 1):], dtype=np.uint8).reshape(N, 7).astype(np.int64)
    code = coord @ (Q ** np.arange(7))
    return coord, code

def normalize(x):
    x = np.asarray(x) % Q
    nz = np.nonzero(x)[0][0]
    return (x * pow(int(x[nz]), Q - 2, Q)) % Q

def point_index(code, x):
    k = int(normalize(x) @ (Q ** np.arange(7)))
    j = int(np.searchsorted(code, k))
    assert code[j] == k, 'not a point'
    return j

def directions():
    """122 projective normals n=(n_s,n_b,n_c,n_f) with 8 n_s^2 + 4 n_b n_f - n_c^2 = 0 (mod 11)."""
    out = set()
    for n in itertools.product(range(Q), repeat=4):
        if any(n) and (8 * n[0] * n[0] + 4 * n[1] * n[3] - n[2] * n[2]) % Q == 0:
            out.add(tuple(normalize(np.array(n))))
    return np.array(sorted(out), dtype=np.int64)

def dir_point(n, z):
    """point at infinity with direction n and offset z (blocked by coset v iff n.v == z)."""
    ns, nb, nc, nf = [int(t) for t in n]
    x1, x2, x3, x6 = ns, nf, (-nc * INV2) % Q, nb
    return np.array([0, x1, x2, x3, (-z) % Q, (2 * x1) % Q, x6], dtype=np.int64)

def coset_lift_points(s, b, c, f):
    """the 11 affine points of the line with coset (s,b,c,f): (a,b,c,e,f)=(lam,b,c,s+9 lam,f)."""
    pts = []
    for lam in range(Q):
        a, e = lam, (s + 9 * lam) % Q
        pts.append(np.array([1, a, b, c, (c * c - a * e - b * f) % Q, e, f], dtype=np.int64))
    return pts

def ncoset(v):
    s, b, c, f = v
    return None
