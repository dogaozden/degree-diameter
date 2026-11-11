# r2sweep.py: exhaustive k=3 orbit families for Haar graphs H(G,S), D = 7, |S| = 5 (round 2 of the (5,7) raise).
# Family: S = {e, t} + one alpha-orbit {x, ax, a^2x} with t in Fix(alpha) (WLOG e in S: left-translating S is an isomorphism).
# G = H1 x ... x Hr x Z_n (cyclic factor last). alpha = conj(c) (c of order 3 up to conjugacy, or 1) composed with z -> r z.
# BFS check and orbit finder are round 1's fam.py (ecc_ok, family). Works from multiplication tables, so it reaches
# groups outside round 1's haar_sym grammar.
# usage: python3 r2sweep.py NAME [NAME ...]   (NAME from CATALOG below, or "all")
import sys, os, time, itertools
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'raise-d5D7-tools'))
import numpy as np
from fam import ecc_ok, family

# ---------- permutation groups ----------
def closure(gens):
    n = len(gens[0]); e = tuple(range(n))
    els = [e]; seen = {e}; i = 0
    while i < len(els):
        x = els[i]; i += 1
        for g in gens:
            y = tuple(g[j] for j in x)
            if y not in seen:
                seen.add(y); els.append(y)
    return els

def perm_table(els):
    """multiplication table, index of els[i] o els[j] (identity must be els[0])."""
    N = len(els); ix = {p: k for k, p in enumerate(els)}
    arr = np.array(els, dtype=np.int64)
    M = np.empty((N, N), dtype=np.int32)
    for i in range(N):
        prod = arr[i][arr]                              # row j = els[i] o els[j]
        M[i] = [ix[tuple(r)] for r in prod.tolist()]
    return M

def product(M1, M2):
    n1, n2 = M1.shape[0], M2.shape[0]
    T = M1[:, None, :, None].astype(np.int64) * n2 + M2[None, :, None, :]
    return T.reshape(n1 * n2, n1 * n2).astype(np.int32)

def cyclic(n):
    i = np.arange(n); return ((i[:, None] + i[None, :]) % n).astype(np.int32)

def ord_mod(a, p):
    y, o = a % p, 1
    while y != 1: y = y * a % p; o += 1
    return o

def prim_mod(p):
    return next(a for a in range(2, p) if ord_mod(a, p) == p - 1)

def sym(n):
    return closure([tuple([1, 0] + list(range(2, n))), tuple(list(range(1, n)) + [0])])

def alt(n):
    if n == 4: return closure([(1, 2, 0, 3), (1, 0, 3, 2)])
    if n == 5: return closure([(1, 2, 0, 3, 4), (1, 2, 3, 4, 0)])

def mobius(p, pgl):
    """PGL(2,p) or PSL(2,p) acting on the projective line {0..p-1, inf = p}."""
    inf = p; g = prim_mod(p); m = g if pgl else g * g % p
    t = [(x + 1) % p for x in range(p)] + [inf]
    mu = [(m * x) % p for x in range(p)] + [inf]
    ni = [inf] + [(-pow(x, p - 2, p)) % p for x in range(1, p)] + [0]
    return closure([tuple(t), tuple(mu), tuple(ni)])

def affine_p(p):
    g = prim_mod(p)
    return closure([tuple((x + 1) % p for x in range(p)), tuple((g * x) % p for x in range(p))])

def gf(p, k, mod):
    """GF(p^k) with x^k = -(mod[0] + mod[1] x + ... ) ; elements are ints sum c_i p^i."""
    q = p ** k
    def tv(x): return [(x // p ** i) % p for i in range(k)]
    def ti(v): return sum(c * p ** i for i, c in enumerate(v))
    def mul(x, y):
        a, b = tv(x), tv(y); r = [0] * (2 * k - 1)
        for i in range(k):
            for j in range(k): r[i + j] = (r[i + j] + a[i] * b[j]) % p
        for d in range(2 * k - 2, k - 1, -1):
            c = r[d]
            if c:
                r[d] = 0
                for i in range(k): r[d - k + i] = (r[d - k + i] - c * mod[i]) % p
        return ti(r[:k])
    return q, mul

def agl_field(p, k, mod, semilinear):
    """AGL(1,q) (or AGammaL(1,q) with the Frobenius) acting on GF(q)."""
    q, mul = gf(p, k, mod)
    def order(z):
        y, o = z, 1
        while y != 1: y = mul(y, z); o += 1
        return o
    zeta = next(z for z in range(2, q) if order(z) == q - 1)
    def add1(x):   # x + 1 in GF(q): coefficient of p^0 shifted (char p)
        v = [(x // p ** i) % p for i in range(k)]; v[0] = (v[0] + 1) % p
        return sum(c * p ** i for i, c in enumerate(v))
    gens = [tuple(add1(x) for x in range(q)), tuple(mul(zeta, x) for x in range(q))]
    if semilinear:
        def frob(x):
            y = 1
            for _ in range(p): y = mul(y, x)
            return y
        gens.append(tuple(frob(x) for x in range(q)))
    return closure(gens)

def linear(p, mats):
    """matrix group over GF(p) acting on the nonzero vectors of GF(p)^2."""
    vecs = [v for v in itertools.product(range(p), repeat=2) if v != (0, 0)]
    ix = {v: i for i, v in enumerate(vecs)}
    gens = [tuple(ix[((a * x + b * y) % p, (c * x + d * y) % p)] for x, y in vecs) for (a, b, c, d) in mats]
    return closure(gens)

def H(name):
    if name == 'S3': return sym(3)
    if name == 'S4': return sym(4)
    if name == 'S5': return sym(5)
    if name == 'A4': return alt(4)
    if name == 'A5': return alt(5)
    if name == 'SL23': return linear(3, [(1, 1, 0, 1), (0, 2, 1, 0)])
    if name == 'SL27': return linear(7, [(1, 1, 0, 1), (0, 6, 1, 0), (3, 0, 0, 5)])
    if name == 'PGL25': return mobius(5, True)
    if name == 'PSL27': return mobius(7, False)
    if name == 'PGL27': return mobius(7, True)
    if name == 'AGL17': return affine_p(7)
    if name == 'AGL111': return affine_p(11)
    if name == 'AGL15': return affine_p(5)
    if name == 'AGL18': return agl_field(2, 3, [1, 1, 0], False)
    if name == 'AGaL18': return agl_field(2, 3, [1, 1, 0], True)
    if name == 'AGL19': return agl_field(3, 2, [1, 0], False)
    if name == 'AGaL19': return agl_field(3, 2, [1, 0], True)
    raise KeyError(name)

_TABLES = {}
def factor_table(name):
    if name not in _TABLES: _TABLES[name] = perm_table(H(name))
    return _TABLES[name]

def build_group(spec):
    """spec: list of factor names; a name 'Z<n>' is the cyclic factor (must be last)."""
    M = None
    for nm in spec:
        T = cyclic(int(nm[1:])) if nm.startswith('Z') else factor_table(nm)
        M = T if M is None else product(M, T)
    return M

def inverse_table(M):
    N = M.shape[0]; inv = np.empty(N, dtype=np.int64)
    r, c = np.nonzero(M == 0); inv[r] = c
    return inv

def alpha_candidates(M, inv, n_cyc):
    N = M.shape[0]; idn = np.arange(N, dtype=np.int64)
    cube_e = M[M[idn, idn], idn] == 0
    o3 = [x for x in range(1, N) if cube_e[x]]
    seen = set(); reps = []
    for x in o3:
        if x in seen: continue
        seen |= set(M[M[:, x], inv].tolist())      # conjugacy class of x
        reps.append(x)
    rs = [1]
    if n_cyc > 2: rs += [r for r in range(2, n_cyc) if np.gcd(r, n_cyc) == 1 and pow(r, 3, n_cyc) == 1]
    out = []
    for c in [None] + reps:
        for r in rs:
            a = idn.copy()
            if c is not None: a = M[M[c, :], inv[c]].astype(np.int64)     # x -> c x c^-1
            if r != 1: a = ((a // n_cyc) * n_cyc + ((a % n_cyc) * r) % n_cyc)  # z -> r z applied after conj
            if np.array_equal(a, idn): continue
            if not (a[a[a]] == idn).all(): continue                         # order exactly 3
            out.append(((c, r), a))
    return out

def run(name, spec, verbose=True):
    t0 = time.time()
    M = build_group(spec); N = M.shape[0]; inv = inverse_table(M); e = 0
    n_cyc = int(spec[-1][1:]) if spec[-1].startswith('Z') else 1
    fams = alpha_candidates(M, inv, n_cyc)
    hits = []
    for key, a in fams:
        fix, orbits = family(N, M, a, e)
        hit = None; ntried = 0
        for t in fix:
            if t == e: continue
            for o in orbits:
                S = [e, int(t)] + o
                if len(set(S)) != 5: continue
                ntried += 1
                if ecc_ok(N, M, S, [int(inv[s]) for s in S], e): hit = S; break
            if hit: break
        if verbose: print(f"{name} N={N} alpha(c,r)={key} |Fix|={len(fix)} orbits={len(orbits)} tried={ntried} HIT={hit}", flush=True)
        if hit:
            hits.append((key, hit)); break
    if verbose: print(f"{name} N={N} families={len(fams)} hits={len(hits)} t={time.time()-t0:.0f}s", flush=True)
    return N, hits

CATALOG = {}
def reg(name, spec): CATALOG[name] = spec
reg('PGL25xZ13', ['PGL25', 'Z13'])          # the record group (validation)
reg('PGL25xZ14', ['PGL25', 'Z14'])
reg('A5xZ27', ['A5', 'Z27'])
for n in range(66, 71): reg(f'S4xZ{n}', ['S4', f'Z{n}'])
for n in range(66, 71): reg(f'SL23xZ{n}', ['SL23', f'Z{n}'])
for n in range(131, 142): reg(f'A4xZ{n}', ['A4', f'Z{n}'])
reg('PGL27xZ5', ['PGL27', 'Z5'])
reg('PSL27xZ10', ['PSL27', 'Z10'])
reg('SL27xZ5', ['SL27', 'Z5'])
reg('AGaL18xZ10', ['AGaL18', 'Z10'])
reg('AGL18xZ28', ['AGL18', 'Z28'])
reg('AGL18xZ29', ['AGL18', 'Z29'])
reg('AGaL19xZ11', ['AGaL19', 'Z11'])
reg('AGL19xZ22', ['AGL19', 'Z22'])
reg('AGL19xZ23', ['AGL19', 'Z23'])
reg('AGL111xZ15', ['AGL111', 'Z15'])
reg('AGL17xZ38', ['AGL17', 'Z38'])
reg('AGL17xZ39', ['AGL17', 'Z39'])
reg('AGL17xZ40', ['AGL17', 'Z40'])
reg('S3xS4xZ11', ['S3', 'S4', 'Z11'])
reg('A4xA4xZ11', ['A4', 'A4', 'Z11'])
reg('S3xA4xZ22', ['S3', 'A4', 'Z22'])
reg('S3xA4xZ23', ['S3', 'A4', 'Z23'])

# batch 2 (round 2): non-cyclic products and AGL(1,5)
reg('A4xZ2xZ66', ['A4', 'Z2', 'Z66']); reg('A4xZ2xZ67', ['A4', 'Z2', 'Z67']); reg('A4xZ2xZ68', ['A4', 'Z2', 'Z68'])
reg('A4xZ2xZ69', ['A4', 'Z2', 'Z69']); reg('A4xZ2xZ70', ['A4', 'Z2', 'Z70'])
reg('A4xZ3xZ44', ['A4', 'Z3', 'Z44']); reg('A4xZ3xZ45', ['A4', 'Z3', 'Z45']); reg('A4xZ3xZ46', ['A4', 'Z3', 'Z46']); reg('A4xZ3xZ47', ['A4', 'Z3', 'Z47'])
reg('S3xS3xZ44', ['S3', 'S3', 'Z44']); reg('S3xS3xZ45', ['S3', 'S3', 'Z45']); reg('S3xS3xZ46', ['S3', 'S3', 'Z46']); reg('S3xS3xZ47', ['S3', 'S3', 'Z47'])
reg('S4xZ3xZ22', ['S4', 'Z3', 'Z22']); reg('S4xZ3xZ23', ['S4', 'Z3', 'Z23'])
reg('A5xZ2xZ14', ['A5', 'Z2', 'Z14'])
reg('PSL27xZ2xZ5', ['PSL27', 'Z2', 'Z5'])
reg('AGL18xZ2xZ14', ['AGL18', 'Z2', 'Z14'])
reg('AGL19xZ2xZ11', ['AGL19', 'Z2', 'Z11'])
reg('AGL15xZ79', ['AGL15', 'Z79']); reg('AGL15xZ80', ['AGL15', 'Z80']); reg('AGL15xZ81', ['AGL15', 'Z81'])
reg('AGL15xZ82', ['AGL15', 'Z82']); reg('AGL15xZ83', ['AGL15', 'Z83']); reg('AGL15xZ84', ['AGL15', 'Z84']); reg('AGL15xZ85', ['AGL15', 'Z85'])
reg('S3xZ2xZ131', ['S3', 'Z2', 'Z131'])

if __name__ == '__main__':
    names = sys.argv[1:] or ['PGL25xZ13']
    if names == ['all']: names = list(CATALOG)
    for nm in names:
        if nm not in CATALOG: print('unknown', nm, flush=True); continue
        run(nm, CATALOG[nm])
