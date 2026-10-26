"""W(q), q even, with the Klein duality, for the duality polygon cover at (11,5).

Points: normalized vectors of PG(3,q). Symplectic form B(x,y) = x0y1+x1y0+x2y3+x3y2 (char 2).
Lines: totally isotropic lines. Klein duality: line span(x,y) -> point (p02 : p13 : p03 : p12),
point P -> line spanned by the images of the q+1 lines through P.
"""
import itertools, sys, json

POLY = {2: 0b11, 4: 0b111, 8: 0b1011, 16: 0b10011, 32: 0b100101}

def field(q):
    deg = q.bit_length() - 1
    poly = POLY[q]
    mul = [[0] * q for _ in range(q)]
    for a in range(q):
        for b in range(q):
            r = 0
            x, y = a, b
            while y:
                if y & 1:
                    r ^= x
                y >>= 1
                x <<= 1
                if x & q:
                    x ^= poly
            mul[a][b] = r
    inv = [0] * q
    for a in range(1, q):
        for b in range(1, q):
            if mul[a][b] == 1:
                inv[a] = b
    return mul, inv

def build(q):
    mul, inv = field(q)
    def norm(v):
        for c in v:
            if c:
                s = inv[c]
                return tuple(mul[s][x] for x in v)
        return None
    pts = [v for v in itertools.product(range(q), repeat=4) if norm(v) == v]
    idx = {v: i for i, v in enumerate(pts)}
    def B(x, y):
        return mul[x[0]][y[1]] ^ mul[x[1]][y[0]] ^ mul[x[2]][y[3]] ^ mul[x[3]][y[2]]
    def span(x, y):
        s = {idx[x], idx[y]}
        for a in range(q):
            v = tuple(x[k] ^ mul[a][y[k]] for k in range(4))
            s.add(idx[norm(v)])
        return frozenset(s)
    lines = {}
    for i, x in enumerate(pts):
        for j in range(i + 1, len(pts)):
            y = pts[j]
            if B(x, y) == 0:
                s = span(x, y)
                if s not in lines:
                    lines[s] = (x, y)
    L = sorted(lines, key=lambda s: sorted(s))
    lidx = {s: i for i, s in enumerate(L)}
    n = len(pts)
    assert n == len(L) == (q + 1) * (q * q + 1)
    # Klein duality on lines
    dl = []
    for s in L:
        x, y = lines[s]
        p = lambda i, j: mul[x[i]][y[j]] ^ mul[x[j]][y[i]]
        v = (p(0, 2), p(1, 3), p(0, 3), p(1, 2))
        dl.append(idx[norm(v)])
    assert len(set(dl)) == n
    # points -> lines
    pt_lines = [[] for _ in range(n)]
    for li, s in enumerate(L):
        for pi in s:
            pt_lines[pi].append(li)
    dp = []
    for pi in range(n):
        img = frozenset(dl[li] for li in pt_lines[pi])
        assert img in lidx, "pencil image not a line"
        dp.append(lidx[img])
    assert len(set(dp)) == n
    # incidence preservation: P in line s  =>  dl[s] in line dp[P]
    for li, s in enumerate(L):
        for pi in s:
            assert dl[li] in L[dp[pi]]
    # Frobenius on points and lines
    sq = [mul[a][a] for a in range(q)]
    fp = [idx[norm(tuple(sq[c] for c in v))] for v in pts]
    fl = [lidx[frozenset(fp[pi] for pi in s)] for s in L]
    return pts, [sorted(s) for s in L], dp, dl, fp, fl

if __name__ == "__main__":
    q = int(sys.argv[1])
    pts, L, dp, dl, fp, fl = build(q)
    n = len(pts)
    # delta = Klein o Frob^m ; delta(P) = dp[fp^m(P)], delta(L) = dl[fl^m(L)]
    def frob_pow(perm, m):
        r = list(range(n))
        for _ in range(m):
            r = [perm[x] for x in r]
        return r
    best = None
    for m in range(0, 8):
        fpm, flm = frob_pow(fp, m), frob_pow(fl, m)
        d_pt = [dp[fpm[x]] for x in range(n)]   # point -> line
        d_ln = [dl[flm[x]] for x in range(n)]   # line -> point
        # incidence check
        ok = all(d_ln[li] in L[d_pt[pi]] for li in range(n) for pi in L[li])
        sq_fix = sum(1 for x in range(n) if d_ln[d_pt[x]] == x)
        absol = sum(1 for x in range(n) if x in L[d_pt[x]])
        print(f"m={m} duality={ok} delta^2 fixes {sq_fix}/{n} points, absolute points {absol}")
        if ok and sq_fix == n and best is None:
            best = m
    out = {"q": q, "points": [list(v) for v in pts], "lines": L, "klein_pt": dp, "klein_ln": dl,
           "frob_pt": fp, "frob_ln": fl, "polarity_m": best}
    json.dump(out, open(f"w{q}.json", "w"))
    print("polarity m =", best)
