"""dmio.py: helpers for Condition-A experiments on the split Cayley hexagon H(q), q an odd prime (5, 7).

load(q) -> H with H.q, H.N (points; vertex ids 0..N-1 points, N..2N-1 lines), H.lines[l] (q+1 point ids of line l),
  H.coords[p] (7-tuple of ints mod q: the point's vector on X0X4+X1X5+X2X6 = X3^2, first nonzero coordinate 1),
  H.flags: flag index i = l*(q+1)+k is the flag (point H.lines[l][k], line l).
B(x, y): polar form; chi(a): quadratic character (+1 / -1, chi(0) = 0).
write_dm(H, nu, path, sig=None): solution file for dmfast / lift2 (DM=1): nu = list of 0/1 per flag (hexagon
  voltage 3*nu in Z6), sig = matching point -> line index (random if None).
score_condA(H, path): runs ./dmfast q with NOROUTE=1 ITERS=0 and returns (failing opposite pairs, percent).
  Condition A for an opposite same-colour pair (v,u): the q+1 hexagon geodesics from v to u do NOT all have the same
  nu-parity.  A random nu fails on a fraction 2^-q of the pairs (q=5: 3.1 %, q=7: 0.78 %).
"""
import random, struct, subprocess, os, re

HERE = os.path.dirname(os.path.abspath(__file__))


class Hex:
    pass


def load(q):
    H = Hex(); H.q = q
    with open(os.path.join(HERE, 'hex', f'hex_q{q}.bin'), 'rb') as f:
        qq, N, L = struct.unpack('3i', f.read(12))
        Q1 = q + 1
        H.lines = [list(struct.unpack(f'{Q1}i', f.read(4 * Q1))) for _ in range(L)]
        raw = f.read(7 * N)
    H.N = N
    H.coords = [tuple(raw[7 * i:7 * i + 7]) for i in range(N)]
    H.flags = [(H.lines[l][k], l) for l in range(L) for k in range(Q1)]
    H.lines_on = [[] for _ in range(N)]
    for l, pts in enumerate(H.lines):
        for p in pts:
            H.lines_on[p].append(l)
    return H


def B(q, x, y):
    return (x[0] * y[4] + x[4] * y[0] + x[1] * y[5] + x[5] * y[1] + x[2] * y[6] + x[6] * y[2] - 2 * x[3] * y[3]) % q


def chi(q, a):
    a %= q
    if a == 0:
        return 0
    return 1 if pow(a, (q - 1) // 2, q) == 1 else -1


def write_dm(H, nu, path, sig=None):
    q, N = H.q, H.N
    if sig is None:
        sig = list(range(N)); random.shuffle(sig)
    with open(path, 'w') as f:
        f.write(f"{q} 2 6 7 -1\ncyc 6\n")
        f.write(' '.join(map(str, sig)) + '\n'); f.write(' '.join(map(str, sig)) + '\n')
        f.write(' '.join(['1'] * N) + '\n'); f.write(' '.join(['4'] * N) + '\n')
        f.write(' '.join(str(3 * (int(b) & 1)) for b in nu) + '\n')


def score_condA(H, path):
    env = dict(os.environ, NOROUTE='1', ITERS='0', IN=os.path.abspath(path))
    out = subprocess.run(['./dmfast', str(H.q)], cwd=HERE, env=env, capture_output=True, text=True).stderr
    m = re.search(r'initial cost (\d+) \(([\d.]+)%\)', out)
    return int(m.group(1)), float(m.group(2))
