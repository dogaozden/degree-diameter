#!/usr/bin/env python3
"""c1: choice of the axis (a, a') for the pencil-dual family at q = 9.

Same construction as cells/d10D8_work/pencil_dual.py (Z_m lift of I(H(9)), two parallel edges p -- delta(p) with
voltages 1 + c(p) and q+2 + c(p), hexagon voltages 0), but the two vectors a, a' are given explicitly.
Usage: python3 axis_study.py FAMILY_LIST OUTJSON
"""
import sys, os, json, subprocess, time
import numpy as np
G = '/home/user/degree-diameter/research/squads/cells/d10D8_work'
sys.path.insert(0, G)
from hexlib import load

Q = 9
PHI = '/home/user/degree-diameter/research/squads/r1_d8c/c5/dual9.phi'
HERE = os.path.dirname(os.path.abspath(__file__))
BASES = os.path.join(HERE, 'bases')
GLIFT = os.path.join(G, 'glift')
os.makedirs(BASES, exist_ok=True)


def gf_tables(q):
    """GF(q) tables in the encoding of hexgen2.c (copied from pencil_dual.py)."""
    polys = {4: ([1, 1], 2), 8: ([1, 1, 0], 3), 9: ([1, 0], 2), 16: ([1, 1, 0, 0], 4), 25: ([2, 0], 2),
             27: ([1, 2, 0], 3), 32: ([1, 0, 1, 0, 0], 5)}
    p = next(d for d in range(2, q + 1) if q % d == 0)
    cfs, e = polys.get(q, ([0], 1))
    def dig(x):
        out = []
        for _ in range(e):
            out.append(x % p); x //= p
        return out
    def enc(v):
        s, pw = 0, 1
        for d in v:
            s += d * pw; pw *= p
        return s
    ADD = [[enc([(u + v) % p for u, v in zip(dig(x), dig(y))]) for y in range(q)] for x in range(q)]
    MUL = [[0] * q for _ in range(q)]
    for x in range(q):
        for y in range(q):
            a, b = dig(x), dig(y)
            r = [0] * (2 * e)
            for i in range(e):
                for j in range(e):
                    r[i + j] = (r[i + j] + a[i] * b[j]) % p
            for k in range(2 * e - 2, e - 1, -1):
                f = r[k]
                if not f:
                    continue
                r[k] = 0
                for i in range(e):
                    r[k - e + i] = (r[k - e + i] - f * cfs[i]) % p
            MUL[x][y] = enc(r[:e])
    NEG = [next(y for y in range(q) if ADD[x][y] == 0) for x in range(q)]
    INV = [0] + [next(y for y in range(q) if MUL[x][y] == 1) for x in range(1, q)]
    return ADD, MUL, NEG, INV

ADD, MUL, NEG, INV = gf_tables(Q)
A_ = np.array(ADD, dtype=np.int64); M_ = np.array(MUL, dtype=np.int64)
NEG_ = np.array(NEG, dtype=np.int64); INV_ = np.array(INV, dtype=np.int64)
TWO = ADD[1][1]
PAIRS = [(0, 4), (4, 0), (1, 5), (5, 1), (2, 6), (6, 2)]

N, LP, PL, coord = load(Q)
C = coord.astype(np.int64)
phi = np.fromfile(PHI, dtype=np.int32).astype(np.int64)
assert phi.shape[0] == 2 * N
LPa = np.asarray(LP, dtype=np.int64)


def gsub(x, y):
    return A_[x, NEG_[y]]


def bvec(x, Y):
    """b(x, Y_i) for all rows Y_i of the N x 7 array Y (x is a length-7 vector)."""
    acc = np.zeros(Y.shape[0], dtype=np.int64)
    for i, j in PAIRS:
        acc = A_[acc, M_[Y[:, i], x[j]]]
    t = M_[TWO, M_[Y[:, 3], x[3]]]
    return A_[acc, NEG_[t]]


def quad(x):
    """Q(x) = x0x4 + x1x5 + x2x6 - x3^2 for one vector."""
    s = A_[A_[M_[x[0], x[4]], M_[x[1], x[5]]], M_[x[2], x[6]]]
    return int(gsub(s, M_[x[3], x[3]]))


def qpoints_on_line(a, a2):
    """number of singular projective points on <a, a2> (0 external, 1 tangent, 2 secant, q+1 totally singular)."""
    nz = 0
    vecs = [(1, t) for t in range(Q)] + [(0, 1)]
    for s, t in vecs:
        v = [A_[M_[s, a[i]], M_[t, a2[i]]] for i in range(7)]
        if quad(v) == 0:
            nz += 1
    return nz


def rank1_ok(A, B):
    """rows of (A, B) (2 x k columns per row): True iff all nonzero columns are proportional (rank <= 1)."""
    A = np.asarray(A); B = np.asarray(B)
    mask = (A != 0) | (B != 0)
    R = np.where(A != 0, M_[B, INV_[A]], 9)
    Rmax = np.where(mask, R, -1).max(axis=1)
    Rmin = np.where(mask, R, 100).min(axis=1)
    return (Rmax == Rmin) | (~mask.any(axis=1))


def stats(F1, F2):
    """#axis points, #hexagon lines meeting the axis, #planes pi_p meeting the axis in a projective line."""
    axis = int(((F1 == 0) & (F2 == 0)).sum())
    lines = int(rank1_ok(F1[LPa], F2[LPa]).sum())
    planes_line = 0
    planes_pt = 0
    chunk = 20000
    PLa = np.asarray(PL, dtype=np.int64)
    for s in range(0, N, chunk):
        idx = LPa[PLa[s:s + chunk]].reshape(-1, (Q + 1) ** 2)
        A = F1[idx]; B = F2[idx]
        mask = (A != 0) | (B != 0)
        rk1 = rank1_ok(A, B)
        rk0 = ~mask.any(axis=1)
        planes_line += int((rk1 & ~rk0).sum())
        planes_pt += 0
    return dict(axis_pts=axis, lines_meet_axis=lines, planes_meet_axis_in_line=planes_line)


def pencil_c(a, a2, gen):
    F1 = bvec(a, C); F2 = bvec(a2, C)
    c = np.empty(N, dtype=np.int64)
    zero_t = F2 == 0
    nz_t = ~zero_t
    c[nz_t] = M_[F1[nz_t], INV_[F2[nz_t]]]
    c[zero_t & (F1 != 0)] = Q
    c[zero_t & (F1 == 0)] = -1
    spec = gen.integers(0, Q + 1, N)
    c = np.where(c < 0, spec, c)
    return c, F1, F2


HEADER = None


def write_base(c, m, path):
    f1 = (1 + c) % m
    f2 = (Q + 2 + c) % m
    lines = [f'Z {m}', f'{2 * N}', ' '.join(['0'] * N + ['1'] * N)]
    lines += [f'{p} {N + l} 0' for l in range(N) for p in LP[l]]
    lines += [f'{p} {phi[p]} {f1[p]}' for p in range(N)]
    lines += [f'{p} {phi[p]} {f2[p]}' for p in range(N)]
    with open(path, 'w') as fh:
        fh.write('\n'.join(lines) + '\n')


def glift(path, seed):
    r = subprocess.run(['timeout', '900', 'nice', '-n', '10', GLIFT, path, f'r:64:{seed}'],
                       capture_output=True, text=True, env=dict(os.environ, OMP_NUM_THREADS='1'))
    for line in r.stdout.splitlines():
        if line.startswith('COST'):
            return int(line.split()[1])
    raise RuntimeError(r.stdout + r.stderr)


def evaluate(name, c, ms, seeds=(1, 2, 3)):
    res = {}
    for m in ms:
        path = os.path.join(BASES, f'{name}_m{m}.txt')
        write_base(c, m, path)
        res[m] = [glift(path, s) for s in seeds]
        os.remove(path)
    return res


# ---------------- families of axes -----------------
def pick_points(pred, rng, k, tries=200000):
    out = []
    for _ in range(tries):
        x = int(rng.integers(0, N))
        if pred(x):
            out.append(x)
            if len(out) == k:
                break
    return out


def class_of_pair(a, a2):
    nz = qpoints_on_line(a, a2)
    return {0: 'external', 1: 'tangent', 2: 'secant'}.get(nz, f'totsing{nz}')


def main():
    fams = sys.argv[1].split(',')
    out_json = sys.argv[2]
    ms = [21, 26, 31, 36]
    rng = np.random.default_rng(12345)
    results = []
    pts_on_Q = np.array([quad(C[x]) == 0 for x in range(N)])
    assert pts_on_Q.all(), 'points of H(9) not on the quadric with this form'
    print('check: all points satisfy Q=0', file=sys.stderr)
    t0 = time.time()

    def run(name, a, a2, info, gen=None):
        if gen is None:
            gen = np.random.default_rng(7)
        c, F1, F2 = pencil_c(a, a2, gen)
        st = stats(F1, F2)
        cls = class_of_pair(a, a2)
        cost = evaluate(name, c, ms)
        rec = dict(name=name, cls=cls, **st, info=info, cost=cost)
        results.append(rec)
        print(json.dumps(rec), flush=True)
        print(f'  elapsed {time.time() - t0:.0f}s', file=sys.stderr, flush=True)

    for fam in fams:
        if fam == 'baseline':
            r = np.random.default_rng(1)
            a = r.integers(0, Q, 7); a2 = r.integers(0, Q, 7)
            # replicates pencil_dual.py seed 1 exactly: a, a2, then the spec draw from the same generator
            run('baseline_seed1', a, a2, 'pencil_dual.py seed 1', gen=r)
        elif fam.startswith('rand'):
            for k in range(3):
                a = rng.integers(0, Q, 7); a2 = rng.integers(0, Q, 7)
                run(f'rand{k}', a, a2, 'uniform random a, a2')
        elif fam == 'sec_opp':
            # a = point p0, a2 = point opposite p0 (b != 0, both on Q: secant line)
            for k in range(3):
                p0 = int(rng.integers(0, N))
                x = pick_points(lambda x: int(bvec(C[p0], C[[x]])[0]) != 0, rng, 1)[0]
                run(f'sec_opp{k}', C[p0], C[x], f'p0={p0} x={x} opposite')
        elif fam == 'ts_d2':
            # a = point p0, a2 = point collinear with p0 (b = 0, hexagon line): totally singular
            for k in range(2):
                p0 = int(rng.integers(0, N))
                l = int(PL[p0][k])
                x = [int(y) for y in LP[l] if y != p0][0]
                run(f'ts_d2_{k}', C[p0], C[x], f'p0={p0} x={x} collinear (same hexagon line)')
        elif fam == 'ts_d4':
            # a = point p0, a2 = point at distance 4 (b = 0, not collinear): totally singular non-hexagon line
            for k in range(3):
                p0 = int(rng.integers(0, N))
                def d4(x, p0=p0):
                    if x == p0:
                        return False
                    if int(bvec(C[p0], C[[x]])[0]) != 0:
                        return False
                    return all(x not in LP[l] for l in PL[p0])
                x = pick_points(d4, rng, 1)[0]
                run(f'ts_d4_{k}', C[p0], C[x], f'p0={p0} x={x} distance 4')
        elif fam == 'dual2':
            # a = point p, a2 = delta^2(p) (a point, via phi twice)
            for k in range(3):
                p0 = int(rng.integers(0, N))
                x = int(phi[phi[p0]])
                run(f'dual2_{k}', C[p0], C[x], f'p0={p0} x=delta2(p0)={x}')
        elif fam == 'dual_line':
            # a = point p, a2 = a point on the hexagon line delta(p)
            for k in range(3):
                p0 = int(rng.integers(0, N))
                l = int(phi[p0]) - N
                x = int(LP[l][k])
                run(f'dual_line{k}', C[p0], C[x], f'p0={p0} x={x} on line delta(p0)={l}')
        elif fam in ('external', 'tangent', 'secant'):
            want = {'external': 'external', 'tangent': 'tangent', 'secant': 'secant'}[fam]
            got = 0; tries = 0
            while got < 3 and tries < 20000:
                tries += 1
                a = rng.integers(0, Q, 7); a2 = rng.integers(0, Q, 7)
                if class_of_pair(a, a2) == want:
                    got += 1
                    run(f'{fam}{got}', a, a2, f'rejection sample, class {want}')
            if got < 3:
                print(f'family {fam}: only {got} found in {tries} tries', file=sys.stderr)
        elif fam == 'pt_rand':
            # a = point p0, a2 uniform random vector
            for k in range(3):
                p0 = int(rng.integers(0, N))
                a2 = rng.integers(0, Q, 7)
                run(f'pt_rand{k}', C[p0], a2, f'p0={p0}, a2 random')
        else:
            raise SystemExit(f'unknown family {fam}')
    with open(out_json, 'w') as fh:
        json.dump(results, fh, indent=1)


if __name__ == '__main__':
    main()
