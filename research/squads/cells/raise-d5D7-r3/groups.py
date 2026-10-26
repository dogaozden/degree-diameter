"""groups.py: multiplication tables for the non-abelian candidate groups of order 781..840.

Each group is built from generators by closure, with the identity as element 0, and written in the
"file" format read by bc2 (m, then the m*m table, row-major, mul[x*m+y] = x*y).
usage: python3 -I groups.py NAME OUTFILE       (NAME from the registry at the bottom)
"""
import sys
from itertools import product


def closure(identity, gens, mul):
    elems = [identity]
    index = {identity: 0}
    frontier = [identity]
    while frontier:
        nxt = []
        for x in frontier:
            for g in gens:
                y = mul(x, g)
                if y not in index:
                    index[y] = len(elems)
                    elems.append(y)
                    nxt.append(y)
        frontier = nxt
    return elems, index


def table(elems, index, mul):
    m = len(elems)
    rows = []
    for x in elems:
        rows.append([index[mul(x, y)] for y in elems])
    return m, rows


def direct_with_cyclic(base, z):
    """base = (identity, gens, mul); returns the group base x Z_z."""
    ident, gens, mul = base
    gens2 = [(g, 0) for g in gens] + [(ident, 1)]
    ident2 = (ident, 0)

    def mul2(x, y):
        return (mul(x[0], y[0]), (x[1] + y[1]) % z)
    return ident2, gens2, mul2


def perm_group(gens):
    n = len(gens[0])
    ident = tuple(range(n))

    def mul(p, q):   # apply q then p
        return tuple(p[q[i]] for i in range(n))
    return ident, gens, mul


def affine_gf(p, k, poly_coeffs, units_only=True):
    """AGL(1,p^k) as maps x -> a x + b on GF(p^k) = GF(p)[t]/(f), f given as coefficient list (low to high, monic)."""
    deg = k
    # field elements as tuples of length deg (coefficients of t^0..t^{deg-1})
    def fmul(a, b):
        prod_ = [0] * (2 * deg - 1)
        for i, ai in enumerate(a):
            for j, bj in enumerate(b):
                prod_[i + j] = (prod_[i + j] + ai * bj) % p
        for d in range(2 * deg - 2, deg - 1, -1):
            c = prod_[d]
            if c:
                prod_[d] = 0
                for i in range(deg):
                    prod_[d - deg + i] = (prod_[d - deg + i] - c * poly_coeffs[i]) % p
        return tuple(prod_[:deg])

    def fadd(a, b):
        return tuple((x + y) % p for x, y in zip(a, b))
    field = list(product(range(p), repeat=deg))
    zero = tuple([0] * deg)
    one = tuple([1] + [0] * (deg - 1))
    # map (a, b) -> the affine map x -> a x + b, represented by its values on all field elements
    maps = {}
    for a in field:
        if a == zero:
            continue
        for b in field:
            vals = tuple(fadd(fmul(a, x), b) for x in field)
            maps[(a, b)] = vals
    fidx = {x: i for i, x in enumerate(field)}
    ident = (one, zero)
    gens_ab = [(a, b) for (a, b) in maps if a != one or b != zero]

    def mul(u, v):   # u after v: x -> a_u (a_v x + b_v) + b_u
        au, bu = u
        av, bv = v
        return (fmul(au, av), fadd(fmul(au, bv), bu))
    # keep the group as pairs; closure will generate all of AGL(1,q)
    gens = [(a, zero) for a in field if a != zero and a != one] + [(one, b) for b in field if b != zero]
    gens = [g for g in gens if g != ident]
    return ident, gens, mul


def pgl2_or_psl2(p, special):
    """SL(2,p) if special else GL(2,p) (matrices over GF(p), p prime)."""
    def mul(A, B):
        return ((A[0] * B[0] + A[1] * B[2]) % p, (A[0] * B[1] + A[1] * B[3]) % p,
                (A[2] * B[0] + A[3] * B[2]) % p, (A[2] * B[1] + A[3] * B[3]) % p)
    ident = (1, 0, 0, 1)
    gens = [(1, 1, 0, 1), (0, p - 1, 1, 0)]  # x->x+1 and s
    if not special:
        for a in range(2, p):
            if all(a % q for q in range(2, a)):
                gens.append((a, 0, 0, 1))
                break
        else:
            gens.append((p - 1, 0, 0, 1))
    return ident, gens, mul


def sl_or_psl_subgroup(p, want_psl):
    ident, gens, mul = pgl2_or_psl2(p, True)
    elems, index = closure(ident, gens, mul)
    if want_psl:
        # PSL(2,p) = SL(2,p)/{+-1}: represent each class by its representative with first nonzero...
        # Use the quotient by computing cosets of {I, -I}.
        neg = (p - 1, 0, 0, p - 1)
        classes = {}
        reps = []
        for x in elems:
            if x in classes:
                continue
            y = mul(x, neg)
            classes[x] = len(reps)
            classes[y] = len(reps)
            reps.append(x)
        # quotient group: table on classes
        def qmul(a, b):
            return mul(a, b)
        # build table directly
        m = len(reps)
        rows = []
        ridx = {r: i for i, r in enumerate(reps)}
        ident_c = classes[ident]
        order = [ident_c] + [i for i in range(m) if i != ident_c]
        new_reps = [reps[i] for i in order]
        nidx = {r: i for i, r in enumerate(new_reps)}
        for r in new_reps:
            row = []
            for s in new_reps:
                row.append(nidx[reps[classes[mul(r, s)]]])
            rows.append(row)
        return m, rows
    m = len(elems)
    rows = [[index[mul(x, y)] for y in elems] for x in elems]
    return m, rows


def gen_table(name):
    """Return (m, rows) for NAME."""
    if name == "agl17xz19":
        base = affine_gf(7, 1, [0])  # GF(7): poly irrelevant for k = 1, use coefficient [0] placeholder
        return product_table(base, 19)
    if name == "agl18xz14":
        base = affine_gf(2, 3, [1, 1, 0])  # t^3 + t + 1
        return product_table(base, 14)
    if name == "agl19xz11":
        base = affine_gf(3, 2, [1, 0])     # t^2 + 1
        return product_table(base, 11)
    if name == "s4xz33":
        base = perm_group([(1, 0, 2, 3), (1, 2, 3, 0), (0, 2, 1, 3)])
        return product_table(base, 33)
    if name == "a4xz66":
        base = perm_group([(1, 2, 0, 3), (1, 0, 3, 2)])
        return product_table(base, 66)
    if name == "sl23xz33":
        base = sl_or_psl_subgroup(3, False)
        return product_table(None, 33, prebuilt=base)
    if name == "psl27xz5":
        m, rows = sl_or_psl_subgroup(7, True)
        return product_table(None, 5, prebuilt=(m, rows))
    if name == "a5xz14":
        base = perm_group([(1, 2, 0, 3, 4), (1, 2, 3, 4, 0)])
        return product_table(None, 14, prebuilt=closure_table(base))
    if name == "s5xz7":
        base = perm_group([(1, 0, 2, 3, 4), (1, 2, 3, 4, 0)])
        return product_table(None, 7, prebuilt=closure_table(base))
    if name == "a5xz11":
        return product_table(None, 11, prebuilt=closure_table(perm_group([(1, 2, 0, 3, 4), (1, 2, 3, 4, 0)])))
    if name == "a5xz22":
        return product_table(None, 22, prebuilt=closure_table(perm_group([(1, 2, 0, 3, 4), (1, 2, 3, 4, 0)])))
    if name == "psl27xz4":
        m, rows = sl_or_psl_subgroup(7, True)
        return product_table(None, 4, prebuilt=(m, rows))
    if name == "psl27xz8":
        m, rows = sl_or_psl_subgroup(7, True)
        return product_table(None, 8, prebuilt=(m, rows))
    if name == "s5xz13":
        return product_table(None, 13, prebuilt=closure_table(perm_group([(1, 0, 2, 3, 4), (1, 2, 3, 4, 0)])))
    if name == "s4xz66":
        return product_table(None, 66, prebuilt=closure_table(perm_group([(1, 0, 2, 3), (1, 2, 3, 0), (0, 2, 1, 3)])))
    if name == "agl18xz28":
        return product_table(affine_gf(2, 3, [1, 1, 0]), 28)
    if name == "agl19xz22":
        return product_table(affine_gf(3, 2, [1, 0]), 22)
    if name == "agl17xz38":
        return product_table(affine_gf(7, 1, [0]), 38)
    if name == "sl23xz66":
        return product_table(None, 66, prebuilt=sl_or_psl_subgroup(3, False))
    if name == "sl25xz7":
        m, rows = sl_or_psl_subgroup(5, False)
        return product_table(None, 7, prebuilt=(m, rows))
    raise SystemExit("unknown group " + name)


def closure_table(base):
    ident, gens, mul = base
    elems, index = closure(ident, gens, mul)
    return table(elems, index, mul)


def product_table(base, z, prebuilt=None):
    if prebuilt is not None:
        m, rows = prebuilt
        # cyclic product of a prebuilt table (element list = range(m))
        idx = {}
        elems = [(g, k) for g in range(m) for k in range(z)]
        for i, e in enumerate(elems):
            idx[e] = i
        ident = (0, 0)
        out = []
        for x in elems:
            out.append([idx[((rows[x[0]][y[0]]), (x[1] + y[1]) % z)] for y in elems])
        return len(elems), out
    ident, gens, mul = direct_with_cyclic(base, z)
    elems, index = closure(ident, gens, mul)
    return table(elems, index, mul)


if __name__ == "__main__":
    name, out = sys.argv[1], sys.argv[2]
    m, rows = gen_table(name)
    with open(out, "w") as f:
        f.write(f"{m}\n")
        for r in rows:
            f.write(" ".join(map(str, r)) + "\n")
    print(name, "order", m)
