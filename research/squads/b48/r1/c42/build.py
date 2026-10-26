"""Group tables for card c42 (triangular / monomial groups). Writes int32 N then N*N uint16, identity index 0."""
import sys, math
import numpy as np
sys.path.insert(0, "/home/user/degree-diameter/research/squads/b48/tools")
import groups

def write_bin(T, path):
    with open(path, "wb") as f:
        np.array([len(T)], dtype=np.int32).tofile(f)
        np.ascontiguousarray(T, dtype=np.uint16).tofile(f)

def borel(p):
    """{[[a,b],[0,d]] : a,d in F_p^*, b in F_p}, order p(p-1)^2, identity index 0."""
    elems = [(1, 0, 1)] + [(a, b, d) for a in range(1, p) for b in range(p) for d in range(1, p) if (a, b, d) != (1, 0, 1)]
    idx = {e: i for i, e in enumerate(elems)}
    N = len(elems)
    def mul(g, h):
        a, b, d = g; a2, b2, d2 = h
        return ((a * a2) % p, (a * b2 + b * d2) % p, (d * d2) % p)
    T = np.empty((N, N), dtype=np.uint16)
    for i, g in enumerate(elems):
        T[i] = [idx[mul(g, h)] for h in elems]
    return T

def wreath_Z2(H):
    """H wr Z_2 = (H x H) x| Z_2; element index s*n*n + h1*n + h2."""
    n = len(H)
    M = 2 * n * n
    g = np.arange(M)
    s, h1, h2 = g // (n * n), (g // n) % n, g % n
    # (x,s)(x',t) = (x * sigma^s(x'), s+t), x = (h1,h2), sigma swaps coordinates
    a = np.arange(M)
    A, B = a[:, None], a[None, :]
    sa, x1, x2 = A // (n * n), (A // n) % n, A % n
    tb, y1, y2 = B // (n * n), (B // n) % n, B % n
    # sigma^s(y) : if s==0 keep (y1,y2) else swap
    z1 = np.where(sa == 0, y1, y2)
    z2 = np.where(sa == 0, y2, y1)
    r1 = H[x1, z1]
    r2 = H[x2, z2]
    st = (sa + tb) % 2
    return (st * n * n + r1.astype(np.int64) * n + r2).astype(np.uint16)

def dihedral(n):
    return groups.table(f"dih {n}")

def check_group(T, name):
    groups.check(T)
    N = len(T)
    # associativity spot check on random triples
    rng = np.random.default_rng(5)
    for _ in range(3000):
        x, y, z = rng.integers(0, N, 3)
        assert T[T[x, y], z] == T[x, T[y, z]], "assoc"
    print(name, "N =", N, "ok", flush=True)

if __name__ == "__main__":
    out = sys.argv[1]
    which = sys.argv[2]
    if which == "borel11":
        T = borel(11)
    elif which == "wrZ24":
        T = wreath_Z2(groups.table("cyc 24"))
    elif which == "wrZ25":
        T = wreath_Z2(groups.table("cyc 25"))
    elif which == "wrD12":
        T = wreath_Z2(dihedral(12))
    else:
        T = groups.table(which)
    check_group(T, which)
    write_bin(T, out)
