"""c2 generator: H(q) + 2 extra matchings, cyclic voltage lift over Z_m, m = 5t, t = (q+5)/2 (q prime, gcd(5,t)=1).

Group Z_m = Z_5 x Z_t (CRT): an element is a pair (a, b), a mod 5, b mod t, encoded as x in Z_m with
x = a mod 5 and x = b mod t.

Hexagon voltage on (p, L) (family 'quad'):  label lam(phi(p)) in Z_t, with phi(p) = Q(x_p) / l(x_p)^2 in GF(q) u {inf}
  (Q a random quadratic form, l a random linear form on the 7 coordinates; a degree-0 function on points, so it is
  constant-free of the representative), lam(v) = v mod t for v in 0..q (q = infinity), voltage = (0, lam) in Z_5 x Z_t.
  Family 'lin' uses a random linear form instead (phi = l(x)), family 'zero' uses 0.
Extra matchings j = 1, 2: M_j random permutations, voltage (j, c_j) with c_j in Z_t random (family 'crt'),
  or fully random in Z_m (family 'rnd').

usage: python3 gen.py q family hexfam seed out.txt [extra]
  family: crt | rnd (extra voltages), hexfam: quad | lin | zero | rndh (uniform random in Z_m)
"""
import sys
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/cells/d14D8_work')
from hexlib import load, write_base, hex_edges


def crt(a, b, t, m):
    """element of Z_m = Z_5 x Z_t (gcd(5,t)=1) with components a mod 5, b mod t."""
    for x in range(m):
        if x % 5 == a % 5 and x % t == b % t:
            return x
    raise ValueError


def build(q, extra_fam, hexfam, seed, out_path, t=None):
    N, LP, PL, coord = load(q)
    t = (q + 5) // 2 if t is None else t
    m = 5 * t
    import os
    if os.environ.get('MOD'):          # override m (only for families without CRT: rnd, rndh)
        m = int(os.environ['MOD'])
    rng = np.random.default_rng(seed)
    X = coord.astype(np.int64) % q
    inv = np.array([0] + [pow(int(a), q - 2, q) for a in range(1, q)])
    if hexfam == 'zero':
        volH = np.zeros(LP.shape, dtype=np.int64)
    elif hexfam == 'rndh':
        volH = rng.integers(0, m, LP.shape)
    elif hexfam == 'rdist':         # uniform random, but the q+1 voltages on each line are distinct
        volH = np.argsort(rng.random((LP.shape[0], m)), axis=1)[:, :LP.shape[1]]
    elif hexfam == 'rT':            # hexagon voltages only in the Z_t part (uniform)
        cr = np.array([crt(0, b, t, m) for b in range(t)])
        volH = cr[rng.integers(0, t, LP.shape)]
    elif hexfam == 'r5':            # hexagon voltages only in the Z_5 part (uniform)
        cr = np.array([crt(a, 0, t, m) for a in range(5)])
        volH = cr[rng.integers(0, 5, LP.shape)]
    else:
        if hexfam.startswith('quad'):   # phi(x) = Q(x) / l(x)^2 in GF(q) u {inf}
            Qc = np.triu(rng.integers(0, q, (7, 7)))
            l = rng.integers(0, q, 7)
            Qv = np.einsum('ni,ij,nj->n', X, Qc, X) % q
            lv = (X @ l) % q
            val = np.where(lv == 0, q, (Qv * inv[lv] % q) * inv[lv] % q)
        elif hexfam.startswith('lq'):   # line-dependent: phi_L(x) = Q(x) / l_L(x)^2 with a random linear form l_L per line
            Qc = np.triu(rng.integers(0, q, (7, 7)))
            XL = X[LP]                                          # (L, q+1, 7)
            Lm = rng.integers(0, q, (LP.shape[0], 7))           # one linear form per line
            lv = np.einsum('lki,li->lk', XL, Lm) % q
            Qv = np.einsum('lki,ij,lkj->lk', XL, Qc, XL) % q
            val = np.where(lv == 0, q, (Qv * inv[lv] % q) * inv[lv] % q)
            lam = val % t
            if hexfam.endswith('r'):
                a5 = rng.integers(0, 5, LP.shape)
                cr2 = np.array([[crt(a, b, t, m) for b in range(t)] for a in range(5)])
                volH = cr2[a5, lam]
            else:
                cr = np.array([crt(0, b, t, m) for b in range(t)])
                volH = cr[lam]
            return _finish(q, N, LP, m, t, rng, volH, extra_fam, out_path)
        elif hexfam == 'lin':           # phi(x) = l(x)
            l = rng.integers(0, q, 7)
            val = (X @ l) % q
        else:
            raise ValueError(hexfam)
        lam = val % t                   # label in Z_t of each point
        if hexfam.endswith('r'):        # Z_5 part uniformly random per (line, position), Z_t part from lam
            a5 = rng.integers(0, 5, LP.shape)
            cr2 = np.array([[crt(a, b, t, m) for b in range(t)] for a in range(5)])
            volH = cr2[a5, lam[LP]]
        else:
            cr = np.array([crt(0, b, t, m) for b in range(t)])
            volH = cr[lam[LP]]          # voltage of (line, position) depends on the point only through lam
    return _finish(q, N, LP, m, t, rng, volH, extra_fam, out_path)


def _finish(q, N, LP, m, t, rng, volH, extra_fam, out_path):
    E = [hex_edges(LP, volt=volH)]
    for j, aj in enumerate((1, 2)):     # two extra matchings, Z_5 parts 1 and 2
        M = rng.permutation(N)
        if extra_fam == 'crt':
            c = rng.integers(0, t, N)
            volE = np.array([crt(aj, cc, t, m) for cc in range(t)])[c]
        elif extra_fam == 'rnd':
            volE = rng.integers(0, m, N)
        elif extra_fam == 'c5':     # extra voltages only in Z_5 (uniform in the Z_5 part of each matching: a constant per matching)
            volE = np.full(N, crt(aj, 0, t, m))
        elif extra_fam == 'tt':     # extra voltages uniform in Z_t part, Z_5 part fixed to aj
            cr = np.array([crt(aj, b, t, m) for b in range(t)])
            volE = cr[rng.integers(0, t, N)]
        elif extra_fam == 'const':
            volE = np.full(N, crt(aj, 0, t, m))
        else:
            raise ValueError(extra_fam)
        E.append(np.stack([np.arange(N), M, volE], axis=1))
    write_base(out_path, N, m, np.concatenate(E))
    return m


if __name__ == '__main__':
    q, extra_fam, hexfam, seed, out_path = int(sys.argv[1]), sys.argv[2], sys.argv[3], int(sys.argv[4]), sys.argv[5]
    print(build(q, extra_fam, hexfam, seed, out_path))
