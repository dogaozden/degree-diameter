"""Build permutation-group tables (groups.py format) for simple/centreless groups used by w12.
Usage: python3 mkgroups.py  (writes groups/<name>.bin and prints order/facts)."""
import sys, os
sys.path.insert(0, "/home/user/degree-diameter/research/squads/handsoff-49/tools")
import numpy as np
import groups as G

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "groups")

def gf8_mul(a, b):
    r = 0
    for i in range(3):
        if (b >> i) & 1: r ^= a << i
    for i in (4, 3):
        if (r >> i) & 1: r ^= 0b1011 << (i - 3)
    return r

def gf9_add(x, y):
    return ((x % 3 + y % 3) % 3) + 3 * (((x // 3) + (y // 3)) % 3)

def gf9_mul(x, y):
    a, b, c, d = x % 3, x // 3, y % 3, y // 3
    re = (a * c - b * d) % 3
    im = (a * d + b * c) % 3
    return re + 3 * im

def gf9_inv(x):
    for y in range(1, 9):
        if gf9_mul(x, y) == 1: return y
    raise ValueError

def proj_perm_from_mobius(q_add, q_mul, q_inv, pts, inf, f):
    """f(x) returns the image of affine point x as an element or 'inf'; returns perm on pts + [inf]."""
    perm = []
    for x in pts:
        perm.append(f(x))
    perm.append(inf)
    return perm

def psl2_8():
    # projective line over GF(8): points 0..7 affine, 8 = infinity
    INF = 8
    tr = [ (x ^ 1) for x in range(8)] + [INF]
    mulw = [gf8_mul(2, x) for x in range(8)] + [INF]
    def inv8(x):
        if x == 0: return INF
        for y in range(1, 8):
            if gf8_mul(x, y) == 1: return y
    invp = [inv8(x) for x in range(8)] + [0]
    return [tr, mulw, invp]

def pgl2_9_gens():
    INF = 9
    w = None
    for c in range(1, 9):
        o, y = 1, c
        while y != 1: y = gf9_mul(y, c); o += 1
        if o == 8: w = c; break
    tr = [gf9_add(x, 1) for x in range(9)] + [INF]
    mulw = [gf9_mul(w, x) for x in range(9)] + [INF]
    invp = [gf9_mul(2, gf9_inv(x)) if x else INF for x in range(9)] + [0]  # -1/x : -1 = 2 in GF(9)
    frob = [ (lambda x: gf9_mul(gf9_mul(x, x), x))(x) for x in range(9)] + [INF]
    return w, tr, mulw, invp, frob

def check_order(name, gens, n_pts):
    T = G.t_perm(n_pts, gens)
    N = len(T)
    return T

def write(name, T):
    G.check(T) if len(T) <= 800 else None
    G.write_bin(T, os.path.join(OUT, name + ".bin"))
    N = len(T)
    order = []
    for g in range(N):
        x, o = g, 1
        while x != 0:
            x = int(T[x, g]); o += 1
        order.append(o)
    centre = sum(1 for g in range(N) if (T[g] == T[:, g]).all())
    print(f"{name}: N={N} involutions={sum(1 for o in order if o == 2)} centre={centre} max_order={max(order)}", flush=True)

if __name__ == "__main__":
    which = sys.argv[1:] or ["psl8", "pgl7", "psl9", "a6", "s6", "pgl9", "m10", "psl11", "pgl11", "psl13"]
    for name in which:
        if name == "psl8":
            g = psl2_8()
            T = G.t_perm(9, g)
            write("psl2_8", T)
        elif name in ("pgl7", "psl11", "pgl11", "psl13"):
            spec = {"pgl7": "pgl2 7", "psl11": "psl2 11", "pgl11": "pgl2 11", "psl13": "psl2 13"}[name]
            T = G.table(spec)
            write(name, T)
        elif name in ("psl9", "a6", "s6", "pgl9", "m10"):
            w, tr, mulw, invp, frob = pgl2_9_gens()
            if name == "psl9":
                w2 = gf9_mul(w, w)
                mulw2 = [gf9_mul(w2, x) for x in range(9)] + [9]
                T = G.t_perm(10, [tr, mulw2, invp])
                write(name, T)
            elif name == "a6":
                w2 = gf9_mul(w, w)
                mulw2 = [gf9_mul(w2, x) for x in range(9)] + [9]
                T = G.t_perm(10, [tr, mulw2, invp])
                # PSL(2,9) = A6; same abstract group (kept as a second check of the table)
                write(name, T)
            elif name == "pgl9":
                T = G.t_perm(10, [tr, [gf9_mul(w, x) for x in range(9)] + [9], invp])
                write(name, T)
            elif name == "s6":
                w2 = gf9_mul(w, w)
                mulw2 = [gf9_mul(w2, x) for x in range(9)] + [9]
                T = G.t_perm(10, [tr, mulw2, invp, frob])
                write(name, T)
            elif name == "m10":
                w2 = gf9_mul(w, w)
                mulw2 = [gf9_mul(w2, x) for x in range(9)] + [9]
                # outer element: frob composed with x -> w x (det w is a non-square)
                fw = [frob[gf9_mul(w, x)] if False else None for x in range(9)]
                outer = [ frob[ (gf9_mul(w, x)) ] for x in range(9) ] + [9]
                T = G.t_perm(10, [tr, mulw2, invp, outer])
                write(name, T)
