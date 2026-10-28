#!/usr/bin/env python3
"""Independent checker for the Q(6,8) / H(8) claims. Written from scratch, numpy only.

Claims:
  1. h (q8_h.txt) maps the 37449 singular points of Q(6,8) to singular points, is invertible,
     and has order exactly 63 as a permutation of those points.
  2. Z = union of h-orbits of the 67 representatives (q8_point_reps.txt) has 4041 points, all
     singular, and no two of them are collinear in H(8).
  3. The 3292 spans (q8_lines_3292_span.txt.gz) are totally singular lines of Q(6,8), and
     the 3292 * 9 points they give are pairwise distinct (29628).
  4. K = min(3292, |Z|) and 2*37449*(2K+1).

Negative controls for each check are run at the end; each must be flagged.
"""
import sys
from math import gcd

import numpy as np

CERT = "/home/user/degree-diameter/research/theorems/polylev/certs"
NPTS = 37449          # (8^6-1)/7
NLINES = 3292
NZ_CLAIM = 4041
FAILS = []


def say(*a):
    print(*a, flush=True)


def expect(cond, msg):
    say(("  PASS  " if cond else "  FAIL  ") + msg)
    if not cond:
        FAILS.append(msg)
    return bool(cond)


def flagged(cond, msg):
    """Negative control: the checker must flag the bad input (cond True = flagged)."""
    say(("  CONTROL FLAGGED  " if cond else "  CONTROL MISSED   ") + msg)
    if not cond:
        FAILS.append("negative control missed: " + msg)
    return bool(cond)


# ---------------------------------------------------------------- GF(8)
# GF(2)[w]/(w^3+w+1); element a0 + a1 w + a2 w^2 is coded as a0 + 2 a1 + 4 a2.
def _gmul(a, b):
    r = 0
    for i in range(3):
        if (b >> i) & 1:
            r ^= a << i
    for bit in (4, 3):
        if (r >> bit) & 1:
            r ^= 0b1011 << (bit - 3)  # x^3 = x + 1
    return r


MUL = np.array([[_gmul(a, b) for b in range(8)] for a in range(8)], dtype=np.uint8)
INV = np.zeros(8, dtype=np.uint8)
for _a in range(1, 8):
    INV[_a] = int(np.flatnonzero(MUL[_a] == 1)[0])


def field_selftest():
    for a in range(8):
        for b in range(8):
            assert MUL[a, b] == MUL[b, a]
            for c in range(8):
                assert MUL[a, MUL[b, c]] == MUL[MUL[a, b], c]
                assert MUL[a, b ^ c] == (MUL[a, b] ^ MUL[a, c])
    for a in range(1, 8):
        assert MUL[a, INV[a]] == 1
        p = 1
        for _ in range(7):
            p = MUL[p, a]
        assert p == 1
    w = 2
    assert (MUL[MUL[w, w], w] ^ w ^ 1) == 0  # w^3 + w + 1 = 0


# ---------------------------------------------------------------- quadric, polar form
def Q(V):
    """Q(X) = X0X4 + X1X5 + X2X6 - X3^2 (characteristic 2: minus is plus)."""
    V = np.asarray(V, dtype=np.uint8)
    return (MUL[V[..., 0], V[..., 4]] ^ MUL[V[..., 1], V[..., 5]]
            ^ MUL[V[..., 2], V[..., 6]] ^ MUL[V[..., 3], V[..., 3]])


def Bp(X, Y):
    """Polar form. Computed directly as the bilinear part; the self-test compares it with Q(X+Y)+Q(X)+Q(Y)."""
    X = np.asarray(X, dtype=np.uint8)
    Y = np.asarray(Y, dtype=np.uint8)
    out = MUL[X[..., 0], Y[..., 4]] ^ MUL[X[..., 4], Y[..., 0]]
    for i in (1, 2):
        out = out ^ MUL[X[..., i], Y[..., i + 4]] ^ MUL[X[..., i + 4], Y[..., i]]
    return out


def normalize(V):
    """Scale each nonzero row so its first nonzero coordinate is 1."""
    V = np.asarray(V, dtype=np.uint8).reshape(-1, 7)
    nz = V != 0
    assert nz.any(axis=1).all(), "zero vector cannot be normalized"
    f = np.argmax(nz, axis=1)
    lead = V[np.arange(V.shape[0]), f]
    return MUL[INV[lead][:, None], V]


POW8 = 8 ** np.arange(7, dtype=np.int64)


def key(V):
    return np.asarray(V).astype(np.int64).reshape(-1, 7) @ POW8


def all_proj_points():
    """All (8^7-1)/7 normalized points of PG(6,8), built directly from the normalization rule."""
    blocks = []
    for f in range(7):
        k = 6 - f
        n = 8 ** k
        blk = np.zeros((n, 7), dtype=np.uint8)
        blk[:, f] = 1
        if k:
            dig = (np.arange(n, dtype=np.int64)[:, None] >> (3 * np.arange(k, dtype=np.int64))[None, :]) & 7
            blk[:, f + 1:] = dig.astype(np.uint8)
        blocks.append(blk)
    P = np.vstack(blocks)
    assert len(P) == (8 ** 7 - 1) // 7
    return P


def count_singular_nonzero_vectors():
    """Brute force over all 8^7 vectors: number of nonzero v with Q(v)=0 (should be 7*37449)."""
    low = np.arange(8 ** 6, dtype=np.int64)
    dig = ((low[:, None] >> (3 * np.arange(6, dtype=np.int64))[None, :]) & 7).astype(np.uint8)
    total = 0
    for top in range(8):
        V = np.empty((8 ** 6, 7), dtype=np.uint8)
        V[:, :6] = dig
        V[:, 6] = top
        total += int((Q(V) == 0).sum())
    return total - 1


class Points:
    """A set of normalized points with an index table over all 8^7 codes (-1 = not in the set)."""

    def __init__(self, P):
        self.P = np.asarray(P, dtype=np.uint8)
        k = key(self.P)
        assert len(np.unique(k)) == len(k), "duplicate points in set"
        self.map = np.full(8 ** 7, -1, dtype=np.int64)
        self.map[k] = np.arange(len(self.P))

    def lookup(self, V):
        Vn = normalize(V)
        return self.map[key(Vn)], Vn


def matvec(H, V):
    V = np.asarray(V, dtype=np.uint8)
    R = np.zeros(V.shape, dtype=np.uint8)
    for i in range(7):
        acc = np.zeros(V.shape[0], dtype=np.uint8)
        for j in range(7):
            acc ^= MUL[int(H[i, j]), V[:, j]]
        R[:, i] = acc
    return R


def gf_rank(M):
    M = [[int(x) for x in row] for row in M]
    rows, cols = len(M), len(M[0])
    r = 0
    for c in range(cols):
        piv = next((i for i in range(r, rows) if M[i][c] != 0), None)
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        inv = int(INV[M[r][c]])
        M[r] = [int(MUL[inv, x]) for x in M[r]]
        for i in range(rows):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                M[i] = [M[i][k] ^ int(MUL[f, M[r][k]]) for k in range(cols)]
        r += 1
    return r


def cycle_lengths(perm):
    seen = np.zeros(len(perm), dtype=bool)
    lens = []
    for s in range(len(perm)):
        if seen[s]:
            continue
        L, t = 0, s
        while not seen[t]:
            seen[t] = True
            t = perm[t]
            L += 1
        lens.append(L)
    return lens


def perm_order(perm):
    o = 1
    for L in set(cycle_lengths(perm)):
        o = o * L // gcd(o, L)
    return o


def perm_power(perm, k):
    p = np.arange(len(perm))
    for _ in range(k):
        p = perm[p]
    return p


# ---------------------------------------------------------------- collinearity in H(8)
# Tits equations for the Grassmann coordinates p_ij = x_i y_j - x_j y_i (char 2: minus is plus).
TITS = [((1, 2), (3, 4)), ((5, 4), (3, 2)), ((2, 0), (3, 5)),
        ((6, 5), (3, 0)), ((0, 1), (3, 6)), ((4, 6), (3, 1))]


def pl(X, Y, a, b):
    return MUL[X[:, a], Y[:, b]] ^ MUL[X[:, b], Y[:, a]]


def line_mask(X, Y):
    """Rows where the span of X[j], Y[j] is 2-dimensional and satisfies the six Tits equations."""
    P = {(a, b): pl(X, Y, a, b) for a in range(7) for b in range(a + 1, 7)}
    indep = np.zeros(len(X), dtype=bool)
    for v in P.values():
        indep |= (v != 0)
    tits = np.ones(len(X), dtype=bool)
    for l, r in TITS:
        tits &= P[tuple(sorted(l))] == P[tuple(sorted(r))]
    return indep & tits


def collinear_with(x, Y):
    """Mask over rows of Y: x and Y[j] are distinct singular points spanning a line of H(8)."""
    Y = np.asarray(Y, dtype=np.uint8)
    X = np.broadcast_to(np.asarray(x, dtype=np.uint8), Y.shape)
    ok = (Q(X) == 0) & (Q(Y) == 0) & (Bp(X, Y) == 0)   # span totally singular
    return ok & line_mask(X, Y)


def collinear_pairs(Z):
    """Unordered pairs {i<j} of rows of Z that are collinear in H(8). Returns (count, sample)."""
    count, sample = 0, []
    for i in range(len(Z)):
        js = np.flatnonzero(collinear_with(Z[i], Z))
        js = js[js > i]
        count += len(js)
        for j in js[: max(0, 5 - len(sample))]:
            sample.append((i, int(j)))
    return count, sample


# ---------------------------------------------------------------- check 1
def check1(H, pts, label):
    out = {"ok": False, "perm": None, "off": None}
    rk = gf_rank(H)
    say(f"  [{label}] rank over GF(8) = {rk}")
    if rk < 7:
        expect(False, f"[{label}] h is invertible")
        return out
    R = matvec(H, pts.P)
    off = int((Q(R) != 0).sum())
    out["off"] = off
    say(f"  [{label}] singular points whose image is NOT singular: {off}")
    idx, _ = pts.lookup(R)
    notpt = int((idx < 0).sum())
    say(f"  [{label}] images not in the point set: {notpt}")
    if notpt:
        out["ok"] = False
        return out
    bij = len(np.unique(idx)) == len(pts.P)
    say(f"  [{label}] induced map is a bijection of the {len(pts.P)} points: {bij}")
    if not bij:
        return out
    perm = idx.astype(np.int64)
    order = perm_order(perm)
    p63 = perm_power(perm, 63)
    say(f"  [{label}] permutation order on points = {order}; perm^63 = id: {np.array_equal(p63, np.arange(len(perm)))}")
    divs = []
    for d in (1, 3, 7, 9, 21, 63):
        if np.array_equal(perm_power(perm, d), np.arange(len(perm))):
            divs.append(d)
    say(f"  [{label}] divisors d of 63 with perm^d = id: {divs}")
    out.update(ok=(off == 0 and notpt == 0 and bij and order == 63 and np.array_equal(p63, np.arange(len(perm)))),
               perm=perm, order=order, off=off)
    return out


# ---------------------------------------------------------------- check 2
def build_Z(pts, perm, reps):
    rn = normalize(reps)
    say(f"  reps singular: {bool((Q(rn) == 0).all())}; reps already normalized: {bool(np.array_equal(rn, np.asarray(reps, np.uint8)))}")
    ridx, _ = pts.lookup(rn)
    assert (ridx >= 0).all()
    inZ = np.zeros(len(pts.P), dtype=bool)
    sizes, covered = [], 0
    for r in ridx:
        r = int(r)
        if inZ[r]:
            covered += 1
        orb = [r]
        t = int(perm[r])
        while t != r:
            orb.append(t)
            t = int(perm[t])
        inZ[orb] = True
        sizes.append(len(orb))
    say(f"  orbit sizes of the 67 reps: {sorted(sizes)}")
    say(f"  reps lying in an orbit already produced by an earlier rep: {covered}")
    Zi = np.flatnonzero(inZ)
    return Zi, inZ, sizes


def check2(pts, perm, reps):
    Zi, inZ, sizes = build_Z(pts, perm, reps)
    Z = pts.P[Zi]
    say(f"  |Z| = {len(Z)}")
    ok_size = expect(len(Z) == NZ_CLAIM, f"|Z| = {len(Z)} (claim 4041)")
    ok_sing = expect(bool((Q(Z) == 0).all()), "all points of Z are singular on Q(6,8)")
    cnt, sample = collinear_pairs(Z)
    say(f"  unordered collinear pairs in Z: {cnt}  sample: {sample}")
    ok_col = expect(cnt == 0, "no two points of Z are collinear in H(8)")
    return {"Zi": Zi, "Z": Z, "inZ": inZ, "ok": ok_size and ok_sing and ok_col}


# ---------------------------------------------------------------- check 3
def check3(L):
    """L: (n,14) integer array of spans. Returns a dict of counts."""
    n = len(L)
    X = np.asarray(L[:, :7], dtype=np.uint8)
    Y = np.asarray(L[:, 7:], dtype=np.uint8)
    combos = [(a, b) for a in range(8) for b in range(8) if (a, b) != (0, 0)]
    A = np.array([c[0] for c in combos], dtype=np.int64)
    Bc = np.array([c[1] for c in combos], dtype=np.int64)
    V = (MUL[A[None, :, None], X[:, None, :]] ^ MUL[Bc[None, :, None], Y[:, None, :]])  # (n,63,7)
    Qv = Q(V.reshape(-1, 7)).reshape(n, 63)
    zero = ~(V != 0).any(axis=2)                       # (n,63): combo is the zero vector
    ts_bad_lines = (Qv != 0).any(axis=1)               # some nonzero vector of the span is not singular
    dep_lines = zero.any(axis=1)                       # span not 2-dimensional
    V2 = V.reshape(-1, 7).copy()
    zf = zero.reshape(-1)
    V2[zf] = 0
    V2[zf, 0] = 1                                      # placeholder so normalize() can run; flagged via dep_lines
    K = key(normalize(V2)).reshape(n, 63)
    per_line = [np.unique(K[i][~zero[i]]) for i in range(n)]
    sizes = np.array([len(u) for u in per_line])
    allk = np.concatenate(per_line)
    uniq = len(np.unique(allk))
    # Informational: Tits equations for the spanning pairs (basis independent)
    tits = line_mask(X, Y)
    return {
        "n": n,
        "ts_bad": int(ts_bad_lines.sum()),
        "dep": int(dep_lines.sum()),
        "npts_not9": int((sizes != 9).sum()),
        "incidences": int(sizes.sum()),
        "unique_points": int(uniq),
        "keys_per_line": per_line,
        "tits_lines": int(tits.sum()),
        "ts_bad_idx": np.flatnonzero(ts_bad_lines)[:5].tolist(),
    }


# ---------------------------------------------------------------- main
def main():
    say("== field and form self-tests")
    field_selftest()
    say("  GF(8) axioms: ok (brute force); w^3+w+1 = 0 ok")
    rng = np.random.default_rng(1)
    Xr = rng.integers(0, 8, size=(2000, 7)).astype(np.uint8)
    Yr = rng.integers(0, 8, size=(2000, 7)).astype(np.uint8)
    expect(np.array_equal(Bp(Xr, Yr), Q(Xr ^ Yr) ^ Q(Xr) ^ Q(Yr)),
           "polar form equals Q(X+Y)-Q(X)-Q(Y) on random vectors")

    say("== enumerating Q(6,8)")
    nvec = count_singular_nonzero_vectors()
    expect(nvec == 7 * NPTS, f"brute-force count of nonzero singular vectors = {nvec} = 7*37449")
    allp = all_proj_points()
    P = allp[Q(allp) == 0]
    expect(len(P) == NPTS, f"normalized singular points of Q(6,8) = {len(P)} (expect 37449)")
    pts = Points(P)

    # Sanity of the collinearity test itself: each point of H(8) is collinear with q(q+1) = 72 others.
    sample = rng.choice(len(P), size=300, replace=False)
    degs = [int(collinear_with(P[s], P).sum()) for s in sample]
    expect(set(degs) == {72}, f"collinearity degree of 300 sampled points of H(8) is 72 (observed set {sorted(set(degs))})")

    H = np.loadtxt(f"{CERT}/q8_h.txt", dtype=np.int64)
    expect(H.shape == (7, 7) and H.min() >= 0 and H.max() <= 7, f"h is 7x7 with entries in GF(8), shape {H.shape}")
    reps = np.loadtxt(f"{CERT}/q8_point_reps.txt", dtype=np.int64)
    expect(reps.shape == (67, 7), f"67 representative rows, shape {reps.shape}")
    L = np.loadtxt(f"{CERT}/q8_lines_3292_span.txt.gz", dtype=np.int64)
    expect(L.shape == (NLINES, 14), f"3292 span rows of 14 integers, shape {L.shape}")

    say("== claim 1: h on Q(6,8)")
    r1 = check1(H.astype(np.uint8), pts, "h")
    expect(r1["ok"], "claim 1: h preserves Q(6,8) on points, invertible, order 63 on points")
    perm = r1["perm"]

    say("== claim 2: Z")
    r2 = {"ok": False}
    if perm is not None:
        r2 = check2(pts, perm, reps)
    Z = r2.get("Z")
    say("== claim 3: 3292 totally singular lines")
    r3 = check3(L)
    say(f"  spans with a non-singular vector in the span: {r3['ts_bad']}  (first indices {r3['ts_bad_idx']})")
    say(f"  spans that are not 2-dimensional: {r3['dep']}")
    say(f"  lines whose point count is not 9: {r3['npts_not9']}")
    say(f"  total incidences (sum of per-line point counts): {r3['incidences']}")
    say(f"  distinct points over all lines: {r3['unique_points']}  (3292*9 = {NLINES * 9})")
    say(f"  info only: spans satisfying the six Tits equations: {r3['tits_lines']}/{NLINES}")
    ok3 = expect(r3["ts_bad"] == 0 and r3["dep"] == 0 and r3["npts_not9"] == 0
                 and r3["unique_points"] == NLINES * 9,
                 "claim 3: all 3292 lines totally singular, pairwise disjoint (29628 distinct points)")
    # overlap of line points with Z (informational)
    if Z is not None:
        allk = np.unique(np.concatenate(r3["keys_per_line"]))
        zk = key(Z)
        say(f"  info only: line points lying in Z: {int(np.isin(allk, zk).sum())}")

    say("== claim 4")
    ok2 = bool(r2["ok"])
    if ok2 and ok3:
        K = min(NLINES, len(Z))
        val = 2 * NPTS * (2 * K + 1)
        say(f"  K = min(3292, |Z|) = {K}")
        say(f"  2*37449*(2K+1) = {val}")
        expect(True, f"claim 4 computed: K={K}, number={val}")
    else:
        K, val = None, None
        expect(False, "claim 4 not computed because claim 2 or 3 failed")

    say("== negative controls")
    if perm is not None:
        # NC1a: perturb one entry of h; it should stop preserving the quadric or stop being a bijection
        Hb = H.astype(np.uint8).copy()
        Hb[0, 0] ^= 1
        rb = check1(Hb, pts, "h with entry (0,0) changed")
        flagged(not rb["ok"], f"claim 1 flags a perturbed h (singular points mapped off the quadric: {rb.get('off')})")
        # NC1b: h^21 has order 3, h^9 has order 7 on points
        for k in (21, 9):
            pk = perm_power(perm, k)
            ordk = perm_order(pk)
            flagged(ordk != 63, f"claim 1 order test flags h^{k} (order {ordk} != 63)")
    if Z is not None:
        # NC2a: add a point collinear with a point of Z
        nb = pts.P[collinear_with(Z[0], pts.P) & ~r2["inZ"]]
        if len(nb):
            y = nb[:1]
            Z2 = np.vstack([Z, y])
            cnt2, samp2 = collinear_pairs(Z2)
            flagged(cnt2 > 0 and len(Z2) != NZ_CLAIM,
                    f"claim 2 flags Z + point collinear with Z[0] (collinear pairs {cnt2}, sample {samp2}, |Z'|={len(Z2)})")
        # NC2b: add a non-singular point
        Vall = allp[Q(allp) != 0][:1]
        Z3 = np.vstack([Z, Vall])
        flagged(not bool((Q(Z3) == 0).all()), "claim 2 singularity test flags Z + one non-singular point")
    # NC3a: a totally singular line through a point of line 0 but distinct from line 0 (duplicate a line point)
    p0 = normalize(L[0:1, :7])
    z_cands = pts.P[Bp(np.broadcast_to(p0, pts.P.shape), pts.P) == 0]
    line0_keys = np.unique(r3["keys_per_line"][0])
    zk = key(z_cands)
    z_cands = z_cands[(~np.isin(zk, line0_keys)) & (zk != key(p0)[0])]
    z = z_cands[:1]
    L2 = L.copy()
    L2[1, :7] = p0[0]
    L2[1, 7:] = z[0]
    r3b = check3(L2)
    flagged(r3b["unique_points"] < NLINES * 9,
            f"claim 3 disjointness flags line 1 replaced by <p, z>, p on line 0 "
            f"(distinct points {r3b['unique_points']} < {NLINES*9}; ts_bad {r3b['ts_bad']})")
    # NC3b: perturb one coordinate of a spanning vector
    L3 = L.copy()
    L3[5, 2] ^= 1
    r3c = check3(L3)
    flagged(r3c["ts_bad"] > 0 or r3c["dep"] > 0 or r3c["unique_points"] < NLINES * 9,
            f"claim 3 flags a perturbed span (non-singular span vectors on {r3c['ts_bad']} line(s), dep {r3c['dep']})")

    say("== summary")
    if ok2 and ok3 and K is not None:
        say(f"  claims 1-4: PASS; K = {K}; 2*37449*(2K+1) = {val}")
    say(f"  failed checks: {FAILS if FAILS else 'none'}")


if __name__ == "__main__":
    main()
