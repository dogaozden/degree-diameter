"""Permutation-group and GF(p^k) matrix-group tables for bicos (w7).  Writes groups.py format (int32 N, N*N uint16,
identity index 0).  Usage: python3 pgen.py NAME OUT.bin"""
import sys
import itertools
import numpy as np


def perm_closure(gens):
    n = len(gens[0])
    ident = tuple(range(n))
    els = [ident]
    seen = {ident: 0}
    i = 0
    while i < len(els):
        g = els[i]
        i += 1
        for s in gens:
            h = tuple(g[s[t]] for t in range(n))
            if h not in seen:
                seen[h] = len(els)
                els.append(h)
    return els


def perm_table(gens):
    els = perm_closure(gens)
    N = len(els)
    n = len(els[0])
    P = np.array(els, dtype=np.uint64)
    rs = np.random.default_rng(12345)
    for attempt in range(20):
        w = rs.integers(1, 2 ** 62, size=n, dtype=np.uint64) | np.uint64(1)
        codes = (P * w).sum(axis=1, dtype=np.uint64)
        if len(np.unique(codes)) == N:
            break
    else:
        raise SystemExit("hash collision")
    order = np.argsort(codes)
    sorted_codes = codes[order]
    T = np.empty((N, N), dtype=np.uint16)
    Pi = P.astype(np.int64)
    for g in range(N):
        comp = Pi[g][Pi]            # comp[h][t] = g[h[t]]  (product g o h)
        c = (comp.astype(np.uint64) * w).sum(axis=1, dtype=np.uint64)
        pos = np.searchsorted(sorted_codes, c)
        assert (sorted_codes[pos] == c).all()
        T[g] = order[pos].astype(np.uint16)
    return T


def gf_tables(p, k, poly):
    """GF(p^k): elements are ints with base-p digits = coefficients; poly = low->high coefficients of x^k reduction
    (x^k = -(poly[0] + ... ) handled by reducing with the monic modulus x^k = sum c_i x^i)."""
    q = p ** k
    def vec(a):
        return [(a // p ** i) % p for i in range(k)]
    def num(v):
        return sum(v[i] * p ** i for i in range(k))
    def mul(a, b):
        va, vb = vec(a), vec(b)
        prod = [0] * (2 * k - 1)
        for i in range(k):
            for j in range(k):
                prod[i + j] = (prod[i + j] + va[i] * vb[j]) % p
        for d in range(2 * k - 2, k - 1, -1):
            c = prod[d]
            if c:
                prod[d] = 0
                for i in range(k):
                    prod[d - k + i] = (prod[d - k + i] + c * poly[i]) % p
        return num(prod[:k])
    def add(a, b):
        va, vb = vec(a), vec(b)
        return num([(va[i] + vb[i]) % p for i in range(k)])
    MUL = [[mul(a, b) for b in range(q)] for a in range(q)]
    ADD = [[add(a, b) for b in range(q)] for a in range(q)]
    INV = [0] * q
    for a in range(1, q):
        for b in range(1, q):
            if MUL[a][b] == 1:
                INV[a] = b
    NEG = [next(b for b in range(q) if ADD[a][b] == 0) for a in range(q)]
    return q, MUL, ADD, INV, NEG


def pl_gens(p, k, poly, pgl):
    """Generators of PSL(2,q) (pgl=False) or PGL(2,q) acting on the q+1 points of PG(1,q)."""
    q, MUL, ADD, INV, NEG = gf_tables(p, k, poly)
    pts = list(range(q)) + ["inf"]
    idx = {v: i for i, v in enumerate(pts)}
    def mob(a, b, c, d):
        perm = []
        for x in pts:
            if x == "inf":
                nu, de = a, c
            else:
                nu = ADD[MUL[a][x]][b]
                de = ADD[MUL[c][x]][d]
            perm.append(idx["inf"] if de == 0 else idx[MUL[nu][INV[de]]])
        return tuple(perm)
    gen = next(g for g in range(2, q) if _order(g, MUL, q) == q - 1) if q > 2 else 1
    if pgl:
        return [mob(1, 1, 0, 1), mob(gen, 0, 0, 1), mob(0, NEG[1], 1, 0)]
    g2 = MUL[gen][gen]
    return [mob(1, 1, 0, 1), mob(g2, 0, 0, 1), mob(0, NEG[1], 1, 0)]


def _order(g, MUL, q):
    x, o = g, 1
    while x != 1:
        x = MUL[x][g]
        o += 1
    return o


def coord(vals):
    return vals


if __name__ == "__main__":
    name, out = sys.argv[1], sys.argv[2]
    if name == "S7":
        gens = [tuple([1, 0] + list(range(2, 7))), tuple(list(range(1, 7)) + [0])]
    elif name == "S6":
        gens = [tuple([1, 0] + list(range(2, 6))), tuple(list(range(1, 6)) + [0])]
    elif name == "A6":
        gens = [(1, 2, 0, 3, 4, 5), (0, 2, 3, 4, 5, 1)]
    elif name == "S5":
        gens = [tuple([1, 0] + list(range(2, 5))), tuple(list(range(1, 5)) + [0])]
    elif name == "PSL33":
        pts = []
        for v in itertools.product(range(3), repeat=3):
            if any(v) and next(x for x in v if x) == 1:
                pts.append(v)
        pidx = {v: i for i, v in enumerate(pts)}
        def norm(v):
            v = tuple(x % 3 for x in v)
            f = next(x for x in v if x)
            return tuple((x * (1 if f == 1 else 2)) % 3 for x in v)
        gens = []
        for i in range(3):
            for j in range(3):
                if i != j:
                    M = np.eye(3, dtype=int)
                    M[i, j] = 1
                    gens.append(tuple(pidx[norm(M @ np.array(p))] for p in pts))
    elif name.startswith("PSL2_") or name.startswith("PGL2_"):
        pgl = name.startswith("PGL2_")
        spec = name.split("_")[1]
        if "^" in spec:
            p, k = (int(x) for x in spec.split("^"))
        else:
            p, k = int(spec), 1
        # reduction x^k = sum poly[i] x^i for irreducible monic polynomials of GF(p^k)
        poly = {(2, 1): [0], (3, 1): [0], (5, 1): [0], (7, 1): [0], (11, 1): [0], (13, 1): [0], (17, 1): [0],
                (19, 1): [0], (23, 1): [0], (2, 2): [1, 1], (3, 2): [2, 0], (5, 2): [2, 0], (2, 3): [1, 1, 0],
                (2, 4): [1, 1, 0, 0], (3, 3): [1, 1, 0]}[(p, k)]
        gens = pl_gens(p, k, poly, pgl)
    else:
        raise SystemExit("unknown name")
    T = perm_table(gens)
    N = len(T)
    with open(out, "wb") as f:
        np.array([N], dtype=np.int32).tofile(f)
        np.ascontiguousarray(T, dtype=np.uint16).tofile(f)
    print(name, "N =", N)
