"""Split abelian-by-cyclic groups G = M x| Z_k for the big-squad-4-8 job.

M = F_{p1^f1} + ... + F_{pt^ft} (as additive groups), and the generator of Z_k acts on component i by multiplication by
a primitive d_i-th root of unity w_i in F_{p_i^{f_i}} (d_i | k; d_i = 1 is a trivial component). With f_i = ord_{d_i}(p_i)
the component is an irreducible Z_k-module. Metacyclic groups are the case where every f_i = 1; Z_13^2 x| Z_7 (Frobenius,
Singer action) is the single component (13, d=7, f=2).

Element (v, j), v = (v_1..v_t), product (v, j)(w, l) = (v + w^j . w, j + l). Index: j * |M| + (mixed radix of the
component coordinates), identity 0.

Usage:
  python3 abc.py list LO HI [--maxk K] [--nonmeta]   list groups with LO <= |G| <= HI: "k comps |G|" (comps = p:d:f,...)
  python3 abc.py build "k p:d,p:d,..." OUT.bin       write the multiplication table (groups.py .bin format);
                                                    a component p:d@e acts by w^e instead of w
The root w_i is a root of the first irreducible factor of Phi_{d_i} over F_p (deterministic), so "build" is reproducible.
"""
import sys
from itertools import combinations_with_replacement
import numpy as np


def is_prime(n):
    if n < 2:
        return False
    i = 2
    while i * i <= n:
        if n % i == 0:
            return False
        i += 1
    return True


def ordmod(p, d):
    if d == 1:
        return 1
    assert d % p != 0, (p, d)
    x, o = p % d, 1
    while x != 1:
        x = x * p % d
        o += 1
    return o


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


# ---- polynomials over F_p (lists low..high) ----
def pmod(a, m, p):
    a = a[:]
    while len(a) >= len(m):
        c = a[-1] * pow(m[-1], p - 2, p) % p
        s = len(a) - len(m)
        for i, x in enumerate(m):
            a[s + i] = (a[s + i] - c * x) % p
        while a and a[-1] == 0:
            a.pop()
    return a


def pmul(a, b, p):
    r = [0] * (len(a) + len(b) - 1) if a and b else []
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            r[i + j] = (r[i + j] + x * y) % p
    return r


def irreducible_of_degree(f, p, d):
    """first monic irreducible polynomial of degree f over F_p (lexicographic) whose root has multiplicative order d"""
    from itertools import product
    for coeffs in product(range(p), repeat=f):
        m = list(coeffs) + [1]
        if f > 1 and m[0] == 0:
            continue
        # x has order d in F_p[x]/(m)?  and m irreducible (x^(p^f) = x and no smaller field)
        def xpow(e):
            r, b = [1], [0, 1]
            while e:
                if e & 1:
                    r = pmod(pmul(r, b, p), m, p)
                b = pmod(pmul(b, b, p), m, p)
                e >>= 1
            return r
        if xpow(d) != [1]:
            continue
        if any(xpow(d // q) == [1] for q in range(2, d + 1) if d % q == 0 and is_prime(q)):
            continue
        # root of order d with ord_d(p) = f generates F_{p^f}, so m (degree f) is its minimal polynomial: irreducible
        return m
    raise ValueError(f"no element of order {d} of degree {f} over F_{p}")


def comp_matrix(p, d):
    """f x f matrix over F_p of multiplication by a primitive d-th root of unity (companion matrix)"""
    f = ordmod(p, d)
    if d == 1:
        return np.eye(1, dtype=np.int64), 1
    if d == 2:
        return np.array([[p - 1]], dtype=np.int64), 1
    m = irreducible_of_degree(f, p, d)
    C = np.zeros((f, f), dtype=np.int64)
    for i in range(1, f):
        C[i, i - 1] = 1
    for i in range(f):
        C[i, f - 1] = (-m[i]) % p
    return C, f


def build(spec):
    k_str, comps_str = spec.split()
    k = int(k_str)
    comps = []
    for c in comps_str.split(","):
        e = 1
        if "@" in c:                       # p:d@e uses w^e instead of w (e coprime to d): e.g. diag(u, u^e) actions
            c, e = c.split("@")
            e = int(e)
        p, d = map(int, c.split(":")[:2])
        assert is_prime(p) and k % d == 0, c
        C, f = comp_matrix(p, d)
        C0 = C.copy()
        for _ in range(e - 1):
            C = C @ C0 % p
        comps.append((p, d, f, C))
    # coordinates: list of (p) per coordinate
    radix = []
    mats = []
    for p, d, f, C in comps:
        radix += [p] * f
        mats.append(C)
    M = int(np.prod(radix))
    N = M * k
    assert N <= 65535
    # coordinates of every m in M
    coords = np.zeros((M, len(radix)), dtype=np.int64)
    x = np.arange(M)
    for t, r in enumerate(radix):
        coords[:, t] = x % r
        x //= r
    weights = np.cumprod([1] + radix[:-1])
    # action of the generator^j on M, as a permutation of M for each j
    act = np.zeros((k, M), dtype=np.int64)
    for j in range(k):
        newc = np.zeros_like(coords)
        off = 0
        for (p, d, f, C) in comps:
            Cj = np.linalg.matrix_power(C, j) % p if j else np.eye(f, dtype=np.int64)
            # matrix_power can overflow for big entries; do it mod p stepwise instead
            P = np.eye(f, dtype=np.int64)
            for _ in range(j % d if d > 1 else 0):
                P = P @ C % p
            newc[:, off:off + f] = (coords[:, off:off + f] @ P.T) % p
            off += f
        act[j] = newc @ weights
    # addition table on M
    T = np.empty((N, N), dtype=np.uint16)
    mod = np.array(radix)
    for j in range(k):
        for v in range(M):
            g = j * M + v
            # (v, j)(w, l) = (v + act_j(w), j + l)
            w_img = coords[act[j]]                       # coords of act_j(w) for all w
            s = (coords[v][None, :] + w_img) % mod        # (M, ncoords)
            sidx = s @ weights                            # index in M
            for l in range(k):
                T[g, l * M:(l + 1) * M] = ((j + l) % k) * M + sidx
    return T


def listing(lo, hi, maxk=120, nonmeta=False):
    out = []
    primes = [p for p in range(2, hi) if is_prime(p)]
    for k in range(2, maxk + 1):
        if k > hi:
            break
        mlo, mhi = (lo + k - 1) // k, hi // k
        if mhi < 1:
            continue
        # components (p, d) with d | k, d >= 2, p^f <= mhi ; plus trivial components (p, 1)
        cands = []
        for d in divisors(k):
            if d <= 2:
                continue                    # only d >= 3: no trivial (central) or inversion (dihedral-type) components
            for p in primes:
                if d % p == 0:
                    continue                # p | d: F_{p^f} has no element of order d
                f = ordmod(p, d) if d > 1 else 1
                if d == 2 and p == 2:
                    continue
                if p ** f <= mhi:
                    cands.append((p ** f, p, d, f))
        cands.sort()

        def rec(start, prod_, chosen):
            if len(chosen) > 3:
                return
            if prod_ >= mlo and chosen:
                ds = [c[2] for c in chosen]
                from math import lcm
                L = 1
                for x in ds:
                    L = lcm(L, x)
                if L == k and any(d >= 3 for d in ds):
                    if not nonmeta or any(c[3] > 1 for c in chosen) or len({c[1] for c in chosen}) < len(chosen):
                        out.append((k * prod_, k, ",".join(f"{p}:{d}:{f}" for (_, p, d, f) in chosen)))
            for i in range(start, len(cands)):
                q, p, d, f = cands[i]
                if prod_ * q > mhi:
                    break
                rec(i, prod_ * q, chosen + [cands[i]])
        rec(0, 1, [])
    out.sort()
    return out


if __name__ == "__main__":
    if sys.argv[1] == "list":
        lo, hi = int(sys.argv[2]), int(sys.argv[3])
        maxk = int(sys.argv[sys.argv.index("--maxk") + 1]) if "--maxk" in sys.argv else 120
        for N, k, comps in listing(lo, hi, maxk, "--nonmeta" in sys.argv):
            print(k, comps, N)
    elif sys.argv[1] == "build":
        sys.path.insert(0, __file__.rsplit("/", 1)[0])
        import groups
        T = build(sys.argv[2])
        groups.check(T)
        groups.write_bin(T, sys.argv[3])
        print("N =", len(T), "spec", sys.argv[2])
