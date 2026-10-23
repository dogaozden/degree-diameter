#!/usr/bin/env python3
"""Independent checker for Haar-graph record claims (written without reference to the generators).

Usage: python3 check_haar_indep.py [--enc rev] [--poly 'x^2+x+2'] SOL.txt [SOL2.txt ...]

Header: `d D <group spec> n NCYC N NTOT`, then d lines `<index> <description>`; only descriptions are used.
G = <group spec> x Z_NCYC.  Haar graph H(G,S): vertices (g,A),(g,B), edges (g,A)~(s.g,B), s in S.
Right multiplication by G is an automorphism group transitive on each side, so BFS from (e,A) and (e,B) suffices.

Own implementation of: GF(p^k) (add/mul tables from polynomial arithmetic), 2x2 matrices over GF(q) with
integer codes, SL/PSL/PGL enumeration and canonical forms, direct products, BFS via per-generator permutations
of the element list (left multiplication by s and by s^-1).

Field element reading (inferred from the files): integer c0 + c1*p + ... + c_{k-1}*p^(k-1), the element
c0 + c1 x + ... in GF(p)[x]/(f).  Matrix `mat(a,b,c,d)` = [[a,b],[c,d]].  Product description
`prod[<mat>;<mat>] z=Z`.  `--enc rev` reverses the digit order (used to demonstrate a wrong reading fails).
"""
import re
import sys
import time
import numpy as np

# ----------------------------------------------------------------------------- finite fields
def parse_poly(s, p):
    """'x^3+2x+1' -> coefficient list low->high, monic assumed but not required."""
    co = {}
    for term in s.replace(" ", "").split("+"):
        m = re.fullmatch(r"(\d*)(x(\^(\d+))?)?", term)
        assert m and term, f"bad poly term {term!r}"
        c = int(m.group(1)) if m.group(1) else 1
        e = (int(m.group(4)) if m.group(4) else 1) if m.group(2) else 0
        co[e] = (co.get(e, 0) + c) % p
    deg = max(co)
    return [co.get(i, 0) for i in range(deg + 1)]


class Field:
    def __init__(self, q, poly=None, rev=False):
        self.q = q
        p = next(r for r in range(2, q + 1) if q % r == 0)
        k = 0
        t = q
        while t % p == 0:
            t //= p
            k += 1
        assert t == 1, f"{q} not a prime power"
        self.p, self.k = p, k
        if k > 1:
            f = parse_poly(poly, p)
            assert len(f) == k + 1 and f[-1] == 1, f"poly degree/monic mismatch: {f} for q={q}"
        else:
            f = None

        def digits(x):
            d = [(x // p ** i) % p for i in range(k)]
            return d[::-1] if rev else d

        def undigits(d):
            d = d[::-1] if rev else d
            return sum(c * p ** i for i, c in enumerate(d))

        add = np.zeros((q, q), dtype=np.uint16)
        mul = np.zeros((q, q), dtype=np.uint16)
        for x in range(q):
            dx = digits(x)
            for y in range(q):
                dy = digits(y)
                add[x, y] = undigits([(u + v) % p for u, v in zip(dx, dy)])
                if k == 1:
                    mul[x, y] = (x * y) % p
                else:
                    prod = [0] * (2 * k - 1)
                    for i, u in enumerate(dx):
                        for j, v in enumerate(dy):
                            prod[i + j] = (prod[i + j] + u * v) % p
                    for i in range(2 * k - 2, k - 1, -1):  # reduce mod f (monic)
                        c = prod[i]
                        if c:
                            for j in range(k + 1):
                                prod[i - k + j] = (prod[i - k + j] - c * f[j]) % p
                    mul[x, y] = undigits(prod[:k])
        zero = undigits([0] * k)
        one = undigits([1] + [0] * (k - 1))
        assert zero == 0 and one == 1 or rev, "identity encoding"
        self.zero, self.one = zero, one
        self.add, self.mul = add, mul
        self.neg = np.array([int(np.nonzero(add[x] == zero)[0][0]) for x in range(q)], dtype=np.uint16)
        inv = np.zeros(q, dtype=np.uint16)
        for x in range(q):
            if x == zero:
                continue
            r = np.nonzero(mul[x] == one)[0]
            assert len(r) == 1, f"element {x} has no inverse: polynomial {poly} not irreducible?"
            inv[x] = r[0]
        self.inv = inv
        # sanity: associativity/distributivity on random triples
        rng = np.random.default_rng(1)
        x, y, z = (rng.integers(0, q, 2000) for _ in range(3))
        assert (mul[mul[x, y], z] == mul[x, mul[y, z]]).all()
        assert (mul[x, add[y, z]] == add[mul[x, y], mul[x, z]]).all()
        assert (add[add[x, y], z] == add[x, add[y, z]]).all()

    def sub(self, x, y):
        return self.add[x, self.neg[y]]


# ----------------------------------------------------------------------------- matrix groups
class MatGroup:
    """SL / PSL / PGL of 2x2 matrices over GF(q); elements identified by sorted integer codes."""

    def __init__(self, kind, F):
        self.kind, self.F, self.q = kind, F, F.q
        q = F.q
        self.q3, self.q2 = q ** 3, q ** 2
        self.codes = self._enumerate()
        self.order = len(self.codes)
        sl = q * (q * q - 1)
        want = {"sl": sl, "psl": sl // (1 if q % 2 == 0 else 2), "pgl": sl}[kind]
        assert self.order == want, f"{kind}({q}) order {self.order} != {want}"

    def code(self, a, b, c, d):
        q = self.q
        return ((a.astype(np.int64) * q + b) * q + c) * q + d

    def canon_code(self, a, b, c, d):
        """code of canonical representative of the class of the matrix (arrays)."""
        F, k = self.F, self.kind
        if k == "sl":
            return self.code(a, b, c, d)
        if k == "psl":
            c1 = self.code(a, b, c, d)
            n = F.neg
            c2 = self.code(n[a], n[b], n[c], n[d])
            return np.minimum(c1, c2)
        first = np.where(a != 0, a, np.where(b != 0, b, np.where(c != 0, c, d)))
        iv = F.inv[first]
        m = F.mul
        return self.code(m[iv, a], m[iv, b], m[iv, c], m[iv, d])

    def _enumerate(self):
        F, q, k = self.F, self.q, self.kind
        m = F.mul
        r = np.arange(q, dtype=np.uint16)
        if k == "pgl":
            parts = []
            # first nonzero entry normalised to 1
            B, C, D = np.meshgrid(r, r, r, indexing="ij")
            B, C, D = B.ravel(), C.ravel(), D.ravel()
            A = np.full_like(B, 1)
            det = F.sub(m[A, D], m[B, C])
            ok = det != 0
            parts.append(self.code(A[ok], B[ok], C[ok], D[ok]))
            # a = 0, b = 1: det = -c, need c != 0
            C2, D2 = np.meshgrid(r, r, indexing="ij")
            C2, D2 = C2.ravel(), D2.ravel()
            ok = C2 != 0
            z = np.zeros_like(C2[ok])
            parts.append(self.code(z, np.ones_like(z), C2[ok], D2[ok]))
            return np.unique(np.concatenate(parts))
        parts = []
        # a != 0: d = (1 + b c) / a
        nz = np.arange(1, q, dtype=np.uint16)
        for a in nz:  # loop over a keeps temporaries small
            B, C = np.meshgrid(r, r, indexing="ij")
            B, C = B.ravel(), C.ravel()
            d = m[F.inv[a], F.add[1, m[B, C]]]
            A = np.full_like(B, a)
            parts.append(self.canon_code(A, B, C, d))
        # a = 0: b c = -1
        B = nz
        C = F.neg[F.inv[B]]
        for dd in range(q):
            z = np.zeros_like(B)
            parts.append(self.canon_code(z, B, C, np.full_like(B, dd)))
        return np.unique(np.concatenate(parts))

    def decode(self, codes):
        q = self.q
        d = codes % q
        t = codes // q
        c = t % q
        t //= q
        b = t % q
        a = t // q
        return a.astype(np.uint16), b.astype(np.uint16), c.astype(np.uint16), d.astype(np.uint16)

    def parse(self, mat):
        a, b, c, d = mat
        F = self.F
        assert all(0 <= v < self.q for v in mat), f"entry out of field range: {mat}"
        det = int(F.sub(F.mul[a, d], F.mul[b, c]))
        if self.kind in ("sl", "psl"):
            assert det == 1, f"det {det} != 1 for {mat} in {self.kind}"
        else:
            assert det != 0, f"singular {mat}"
        return tuple(np.uint16(v) for v in mat)

    def adj(self, s):
        n = self.F.neg
        a, b, c, d = s
        return (d, n[b], n[c], a)  # inverse up to scalar (exact inverse when det=1)

    def lperm(self, s):
        """perm[i] = index of s * element_i."""
        F = self.F
        m, ad = F.mul, F.add
        a, b, c, d = s
        A, B, C, D = self.decode(self.codes)
        na = ad[m[a, A], m[b, C]]
        nb = ad[m[a, B], m[b, D]]
        nc = ad[m[c, A], m[d, C]]
        nd = ad[m[c, B], m[d, D]]
        cd = self.canon_code(na, nb, nc, nd)
        idx = np.searchsorted(self.codes, cd)
        assert (idx < self.order).all() and (self.codes[idx] == cd).all(), "closure failure"
        return idx.astype(np.int32)

    def ident_index(self):
        one = self.F.one
        cd = self.canon_code(*(np.array([v], dtype=np.uint16) for v in (one, 0, 0, one)))
        i = int(np.searchsorted(self.codes, cd[0]))
        assert self.codes[i] == cd[0]
        return i

    def elem_index(self, mat):
        cd = self.canon_code(*(np.array([v], dtype=np.uint16) for v in mat))
        i = int(np.searchsorted(self.codes, cd[0]))
        assert i < self.order and self.codes[i] == cd[0], f"{mat} not in group"
        return i

    def self_test(self):
        """random associativity / inverse check using the permutations' action: (st)g = s(tg)."""
        rng = np.random.default_rng(7)
        pick = lambda: tuple(np.uint16(v) for v in np.array(self.decode(self.codes[rng.integers(0, self.order, 1)]))[:, 0])
        for _ in range(3):
            s, t = pick(), pick()
            g = rng.integers(0, self.order, 5000)
            # t*g then s*(t*g)  vs  (s t)*g where s t computed as matrix product
            F = self.F
            m, ad = F.mul, F.add
            st = (ad[m[s[0], t[0]], m[s[1], t[2]]], ad[m[s[0], t[1]], m[s[1], t[3]]],
                  ad[m[s[2], t[0]], m[s[3], t[2]]], ad[m[s[2], t[1]], m[s[3], t[3]]])
            p1 = self.lperm(s)[self.lperm(t)[g]]
            p2 = self.lperm(st)[g]
            assert (p1 == p2).all(), "group law inconsistency"


# ----------------------------------------------------------------------------- spec parsing
def parse_factor(tokens, pos, rev, polyover):
    kind = tokens[pos]
    assert kind in ("sl", "psl", "pgl"), f"unsupported group kind {kind}"
    q = int(tokens[pos + 1])
    pos += 2
    poly = None
    if pos < len(tokens) and tokens[pos] == "poly":
        poly = polyover or tokens[pos + 1]
        pos += 2
    F = Field(q, poly, rev)
    return (kind, F), pos


def parse_header(line):
    t = line.split()
    d, D = int(t[0]), int(t[1])
    i = t.index("n")
    spec = t[2:i]
    ncyc, ntot = int(t[i + 1]), int(t[i + 3])
    return d, D, spec, ncyc, ntot


# ----------------------------------------------------------------------------- the check
def check(path, rev=False, polyover=None, log=print):
    t0 = time.time()
    lines = open(path).read().split("\n")
    d, D, spec, ncyc, ntot = parse_header(lines[0])
    log(f"file {path}\nheader: d={d} D={D} spec={' '.join(spec)} NCYC={ncyc} N={ntot}")
    if spec[0] == "prod":
        facs, pos = [], 1
        while pos < len(spec):
            f, pos = parse_factor(spec, pos, rev, polyover)
            facs.append(f)
        assert len(facs) == 2
        prod = True
    else:
        f, pos = parse_factor(spec, 0, rev, polyover)
        assert pos == len(spec)
        facs, prod = [f], False
    groups = [MatGroup(k, F) for k, F in facs]
    for g in groups:
        g.self_test()
    gorder = int(np.prod([g.order for g in groups]))
    NC = ncyc
    N = gorder * NC
    log(f"group order |G|={gorder} (factors {[g.order for g in groups]}), x Z_{NC} -> {N}; vertices 2N={2 * N}")
    assert N == ntot, f"order mismatch with header N={ntot}"

    # parse generators
    gens = []  # (list of per-factor matrices, z)
    for ln in lines[1:1 + d]:
        body = ln.split(None, 1)[1]
        z = int(re.search(r"z=(\d+)", body).group(1))
        mats = [tuple(int(v) for v in mm.split(",")) for mm in re.findall(r"mat\(([^)]*)\)", body)]
        assert len(mats) == len(groups), f"description {ln!r}: expected {len(groups)} matrices"
        assert 0 <= z < NC
        gens.append(([g.parse(mt) for g, mt in zip(groups, mats)], z))
    assert len(gens) == d, "fewer generator lines than d"

    # identity of each generator as group-element id: ig*NC+z, ig = i1*|G2|+i2
    def elem_id(mats, z):
        ig = 0
        for g, mt in zip(groups, mats):
            ig = ig * g.order + g.elem_index(mt)
        return ig * NC + z

    ids = [elem_id(mats, z) for mats, z in gens]
    distinct = len(set(ids))
    log(f"distinct generators (as full group elements): {distinct} of d={d}")

    # permutations of group elements (left mult by s and s^-1), cached per factor-matrix
    cache = {}

    def fperm(gi, mt):
        key = (gi, tuple(int(v) for v in mt))
        if key not in cache:
            cache[key] = groups[gi].lperm(mt)
        return cache[key]

    def full_perm(mats):
        ps = [fperm(gi, mt) for gi, mt in enumerate(mats)]
        if not prod:
            return ps[0]
        n2 = groups[1].order
        return (ps[0].astype(np.int64)[:, None] * n2 + ps[1][None, :]).ravel().astype(np.int32)

    fwd, bwd = [], []
    for (mats, z), gid in zip(gens, ids):
        fwd.append((full_perm(mats), z))
        inv = [groups[gi].adj(mt) for gi, mt in enumerate(mats)]
        bwd.append((full_perm(inv), (-z) % NC))
    # check s^-1 really inverts s on a sample
    rng = np.random.default_rng(3)
    smp = rng.integers(0, gorder, 3000)
    for (pf, _), (pb, _) in zip(fwd, bwd):
        assert (pb[pf[smp]] == smp).all(), "inverse permutation check failed"
    log(f"permutations built ({time.time() - t0:.0f}s)")

    def step(front, perms):
        """image of frontier ids under every generator in perms; returns bool mask over ids."""
        mask = np.zeros(N, dtype=bool)
        ig = front // NC if NC > 1 else front
        zz = front % NC if NC > 1 else None
        for pm, z in perms:
            img = pm[ig].astype(np.int64)
            if NC > 1:
                img = img * NC + (zz + z) % NC
            mask[img] = True
        return mask

    e = 0
    for gi, g in enumerate(groups):
        pass
    eid = 0
    for g in groups:
        eid = eid * g.order + g.ident_index()
    eid = eid * NC + 0

    res = {}
    for side in ("A", "B"):
        visA = np.zeros(N, dtype=bool)
        visB = np.zeros(N, dtype=bool)
        cur_side = side
        (visA if side == "A" else visB)[eid] = True
        front = np.array([eid], dtype=np.int64)
        level, sizes = 0, [1]
        while len(front):
            nxt_vis = visB if cur_side == "A" else visA
            mask = step(front, fwd if cur_side == "A" else bwd)
            new = np.flatnonzero(mask & ~nxt_vis)
            nxt_vis[new] = True
            if len(new) == 0:
                break
            level += 1
            sizes.append(len(new))
            front = new
            cur_side = "B" if cur_side == "A" else "A"
        reached = int(visA.sum() + visB.sum())
        res[side] = dict(ecc=level, reached=reached, sizes=sizes)
        log(f"BFS from {side}: ecc={level} reached {reached} of {2 * N} (unreached {2 * N - reached}); level sizes {sizes}")
    ok_deg = distinct == d
    ok = (ok_deg and all(r["reached"] == 2 * N for r in res.values()) and all(r["ecc"] <= D for r in res.values()))
    verdict = "VALID" if ok else "INVALID"
    log(f"every vertex has exactly {d} distinct neighbours: {ok_deg}")
    log(f"RESULT {verdict} d={d} D={D} eccA={res['A']['ecc']} eccB={res['B']['ecc']} n={2 * N} ({time.time() - t0:.0f}s)")
    return verdict, res


def main():
    args = sys.argv[1:]
    rev, poly = False, None
    while args and args[0].startswith("--"):
        if args[0] == "--enc":
            rev = args[1] == "rev"
            args = args[2:]
        elif args[0] == "--poly":
            poly = args[1]
            args = args[2:]
        else:
            raise SystemExit("unknown option " + args[0])
    for p in args:
        try:
            check(p, rev, poly)
        except AssertionError as ex:
            print(f"RESULT INVALID (assertion) {p}: {ex}")
        print(flush=True)


if __name__ == "__main__":
    main()
