"""w10 group toolkit: build Cayley tables for group families, check them, and write .bin for haar_tab.

Table format (same as tools/groups.py): int32 N, then N*N uint16, row g = g*h, identity index 0.
Generic matrix semidirect product: V x| H, V = GF(p)^d, H = closure of matrix generators over GF(p).
"""
import sys, os, itertools
import numpy as np

TOOLS = "/home/user/degree-diameter/research/squads/handsoff-49/tools"
sys.path.insert(0, TOOLS)
import groups as G  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))


def mat_mul(A, B, p):
    d = len(A)
    return tuple(tuple(sum(A[i][k] * B[k][j] for k in range(d)) % p for j in range(d)) for i in range(d))


def mat_closure(gens, p):
    """Closure of matrix generators; identity first (index 0)."""
    d = len(gens[0])
    I = tuple(tuple(1 if i == j else 0 for j in range(d)) for i in range(d))
    els = [I]
    seen = {I: 0}
    i = 0
    while i < len(els):
        g = els[i]
        i += 1
        for s in gens:
            h = mat_mul(g, s, p)
            if h not in seen:
                seen[h] = len(els)
                els.append(h)
                if len(els) > 20000:
                    raise ValueError("matrix group too big")
    return els, seen


def semidirect_vec(p, d, gens):
    """Table of V x| H, V = GF(p)^d, H = <gens> (list of dxd tuples). Element (v,h) has index v*|H| + h."""
    Hel, Hidx = mat_closure(gens, p)
    Nh = len(Hel)
    Nv = p ** d
    # vectors: index v <-> tuple of d digits base p (digit i = coordinate i)
    vecs = np.array([[(v // p ** i) % p for i in range(d)] for v in range(Nv)], dtype=np.int64)
    pw = np.array([p ** i for i in range(d)], dtype=np.int64)
    Vsum = (((vecs[:, None, :] + vecs[None, :, :]) % p) @ pw).astype(np.int64)  # Nv x Nv
    # MW[h, w] = index of M_h w
    Mh = np.array(Hel, dtype=np.int64)  # Nh x d x d
    MW = np.einsum("hij,wj->hwi", Mh, vecs) % p
    MW = (MW @ pw).astype(np.int64)  # Nh x Nv
    TH = np.empty((Nh, Nh), dtype=np.int64)
    for a in range(Nh):
        for b in range(Nh):
            TH[a, b] = Hidx[mat_mul(Hel[a], Hel[b], p)]
    N = Nv * Nh
    a = np.arange(N)
    av, ah = a // Nh, a % Nh
    VV = Vsum[av[:, None], MW[ah[:, None], av[None, :]]]
    T = VV * Nh + TH[ah[:, None], ah[None, :]]
    return T.astype(np.uint16)


def inv_of(T):
    N = len(T)
    return np.argmax(T == 0, axis=1)


def props(T, name="", full_check=True):
    """Return dict with N, centre size, |G'|, abelianization size, latin/assoc sample check."""
    N = len(T)
    rng = np.random.default_rng(7)
    ok = bool((T[0] == np.arange(N)).all() and (T[:, 0] == np.arange(N)).all())
    for _ in range(200):
        g, h, k = rng.integers(0, N, 3)
        if T[T[g, h], k] != T[g, T[h, k]]:
            ok = False
            break
    if full_check:
        ok = ok and all(len(np.unique(T[g])) == N for g in range(0, N, max(1, N // 200)))
    I = inv_of(T)
    # centre
    centre = int(np.sum(np.all(T == T.T, axis=1)))  # z with zg = gz for all g
    # commutators [a,b] = a^-1 b^-1 a b
    comm = set()
    Ib = I
    for a in range(N):
        row = T[T[Ib[a], Ib[:]], T[a, :]]  # a^-1 b^-1 a b  for all b  (T[ Ib[a], Ib[b] ] = a^-1 b^-1)
        comm.update(np.unique(row).tolist())
    gens = np.array(sorted(comm), dtype=np.int64)
    mask = np.zeros(N, dtype=bool)
    mask[0] = True
    while True:
        el = np.nonzero(mask)[0]
        new = np.unique(T[el[:, None], gens[None, :]].ravel())
        if mask[new].all():
            break
        mask[new] = True
    dG = int(mask.sum())
    return dict(name=name, N=N, centre=centre, derived=dG, ab=N // dG, ok=ok)


def write_bin(T, path):
    with open(path, "wb") as f:
        np.array([len(T)], dtype=np.int32).tofile(f)
        T.astype(np.uint16).tofile(f)


def load_bin(path):
    with open(path, "rb") as f:
        N = int(np.fromfile(f, dtype=np.int32, count=1)[0])
        return np.fromfile(f, dtype=np.uint16, count=N * N).reshape(N, N)


def elem_order(T, g):
    k, x = 1, g
    while x != 0:
        x = T[x, g]
        k += 1
    return k
