"""c5 toolkit: root subgroups (unipotent, via truncated exponential of root vectors of so(G)), split torus elements,
and helpers to write generator files for orbclq.  Standard form G of ovlib (Q = x0x4 + x1x5 + x2x6 - x3^2, q = 11)."""
import sys, os, itertools, random, subprocess, json
sys.path.insert(0, '/home/user/degree-diameter/research/cell147/ovoid')
import ovlib as L
q = 11
G = L.std_gram(q)
ORB = '/home/user/degree-diameter/research/cell147/ovoid/orbclq'
CHECK = '/home/user/degree-diameter/research/cell147/ovoid/checkset.py'
MYDIR = os.path.dirname(os.path.abspath(__file__))
# weights of the 7 coordinates of the split torus diag(a,b,c,s,1/a,1/b,1/c) (eps-coefficients)
W = [(1, 0, 0), (0, 1, 0), (0, 0, 1), (0, 0, 0), (-1, 0, 0), (0, -1, 0), (0, 0, -1)]
POS_ROOTS = [(1, -1, 0), (1, 1, 0), (1, 0, -1), (1, 0, 1), (0, 1, -1), (0, 1, 1), (1, 0, 0), (0, 1, 0), (0, 0, 1)]

def nullspace(rows, n):
    M = [list(r) for r in rows]; piv = []; r = 0
    for c in range(n):
        p = next((i for i in range(r, len(M)) if M[i][c] % q), None)
        if p is None: continue
        M[r], M[p] = M[p], M[r]; s = L.inv(M[r][c], q); M[r] = [x * s % q for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c]:
                f = M[i][c]; M[i] = [(x - f * y) % q for x, y in zip(M[i], M[r])]
        piv.append(c); r += 1
    out = []
    for fc in [c for c in range(n) if c not in piv]:
        v = [0] * n; v[fc] = 1
        for i, c in enumerate(piv): v[c] = (-M[i][fc]) % q
        out.append(v)
    return out

def root_vector(beta):
    """X in so(G) of weight beta (eps-coordinates): X = sum x_ij E_ij over (i,j) with W[i]-W[j] = beta."""
    idx = [(i, j) for i in range(7) for j in range(7)
           if tuple(W[i][k] - W[j][k] for k in range(3)) == tuple(beta)]
    # equations: (X^T G + G X)[a][b] = 0 for all a,b
    rows = {}
    for m, (i, j) in enumerate(idx):
        for b in range(7):
            # X^T G term: (X^T G)[j][b] += X[i][j] * G[i][b]
            rows.setdefault((j, b), [0] * len(idx))[m] += G[i][b]
        for a in range(7):
            # G X term: (G X)[a][j] += G[a][i] * X[i][j]
            rows.setdefault((a, j), [0] * len(idx))[m] += G[a][i]
    eqs = [[x % q for x in r] for r in rows.values()]
    ns = nullspace(eqs, len(idx))
    return idx, ns

def root_element_matrix(beta, which=0):
    idx, ns = root_vector(beta)
    assert len(ns) >= 1, ('no root vector', beta)
    v = ns[which]
    X = [[0] * 7 for _ in range(7)]
    for m, (i, j) in enumerate(idx): X[i][j] = v[m] % q
    return X

def exp_nilp(X, t):
    """exp(tX) = sum_k t^k X^k / k!, valid for X^7 = 0 and k <= 6 (invertible factorials mod 11)."""
    M = L.mat_id(7); P = L.mat_id(7); fact = 1
    for k in range(1, 7):
        P = L.mat_mul(P, X, q)
        fact = fact * k % q
        c = pow(t, k, q) * L.inv(fact, q) % q
        M = [[(M[i][j] + c * P[i][j]) % q for j in range(7)] for i in range(7)]
    return M

def root_elt(beta, t=1, which=0):
    X = root_element_matrix(beta, which)
    M = exp_nilp(X, t)
    assert L.is_isometry(M, G, q), ('not isometry', beta)
    return M

def torus(a, b, c, s=1):
    d = [a % q, b % q, c % q, s % q, L.inv(a, q), L.inv(b, q), L.inv(c, q)]
    return [[d[i] if i == j else 0 for j in range(7)] for i in range(7)]

def mat_order_proj(M):
    return L.mat_order(M, q, limit=10**5)

def write_gens(path, mats, comment=''):
    L.write_gens(path, mats, comment)

def run_orbclq(gens_path, t=20, seed=1, out=None, extra=()):
    cmd = [ORB, gens_path, '-t', str(t), '-s', str(seed)]
    if out: cmd += ['-o', out]
    cmd += list(extra)
    p = subprocess.run(['timeout', '900', 'nice', '-n', '10'] + cmd, capture_output=True, text=True)
    res = None
    for line in p.stdout.splitlines():
        if line.startswith('RESULT'): res = line
    info = [l for l in p.stderr.splitlines() if 'good orbits' in l or 'orbit sizes' in l]
    return res, info

def best_of(res):
    if not res: return None
    for tok in res.split():
        if tok.startswith('best='): return int(tok[5:].split()[0])
    return None

def group_size(mats, limit=5000):
    return L.group_order(mats, q, limit=limit)
