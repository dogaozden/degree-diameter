"""a10: non-faithful single-field groups G = F_q x| Z_k, generator j acts as multiplication by zeta^j,
zeta of exact order d (d | gcd(k, q-1)). Writes groups.py-format table (int32 N, N*N uint16, row g = g*h, identity 0).
Usage: python3 fgroup.py p f k d OUT.bin [e]      (q = p^f; zeta = g^((q-1)/d * e) for a primitive g, e default 1)
       python3 fgroup.py --info p f k d
"""
import sys, itertools
import numpy as np

def is_prime(n):
    return n > 1 and all(n % i for i in range(2, int(n ** 0.5) + 1))

def field(p, f):
    q = p ** f
    if f == 1:
        add = np.array([[(a + b) % p for b in range(p)] for a in range(p)], dtype=np.int64)
        mul = np.array([[(a * b) % p for b in range(p)] for a in range(p)], dtype=np.int64)
        return q, add, mul
    def digits(x):
        return [(x // p ** i) % p for i in range(f)]
    def num(c):
        return sum(c[i] * p ** i for i in range(f))
    # monic irreducible of degree f: no roots-free test by brute force (check no factor of degree <= f/2)
    def polymulmod(a, b, m):
        r = [0] * (2 * f - 1)
        for i, x in enumerate(a):
            for j, y in enumerate(b):
                r[i + j] = (r[i + j] + x * y) % p
        for t in range(len(r) - 1, f - 1, -1):
            c = r[t]
            if c:
                for i in range(f + 1):
                    r[t - f + i] = (r[t - f + i] - c * m[i]) % p
        return r[:f]
    m = None
    for coeffs in itertools.product(range(p), repeat=f):
        cand = list(coeffs) + [1]
        if cand[0] == 0:
            continue
        # irreducible iff x^(p^f) = x mod cand and gcd conditions: brute force: no root of multiplicative order issue;
        # use: the ring F_p[x]/(cand) is a field iff every nonzero element is invertible -> check via order of x
        ok = True
        # check field: x^(q) == x and x^(p^j) != x for proper divisors j of f
        def xpow(e):
            r = [1] + [0] * (f - 1); b = [0, 1] + [0] * (f - 2) if f > 1 else [0]
            while e:
                if e & 1:
                    r = polymulmod(r, b, cand)
                b = polymulmod(b, b, cand)
                e >>= 1
            return r
        xs = [0, 1] + [0] * (f - 2)
        if xpow(q) != xs:
            continue
        for j in range(1, f):
            if f % j == 0 and xpow(p ** j) == xs:
                ok = False
                break
        if ok:
            m = cand
            break
    assert m is not None
    add = np.zeros((q, q), dtype=np.int64)
    mul = np.zeros((q, q), dtype=np.int64)
    D = [digits(x) for x in range(q)]
    for a in range(q):
        for b in range(q):
            add[a, b] = num([(x + y) % p for x, y in zip(D[a], D[b])])
            mul[a, b] = num(polymulmod(D[a], D[b], m))
    return q, add, mul

def primitive(q, add, mul):
    for g in range(1, q):
        x, o = g, 1
        while x != 1:
            x = mul[x, g]; o += 1
        if o == q - 1:
            return g
    raise ValueError

def zeta(p, f, d, e=1):
    q, add, mul = field(p, f)
    assert (q - 1) % d == 0
    g = primitive(q, add, mul)
    z = 1
    base = g
    ex = (q - 1) // d * e
    # z = g^ex
    z = 1
    b = g
    while ex:
        if ex & 1:
            z = mul[z, b]
        b = mul[b, b]
        ex >>= 1
    # check order d
    o, x = 1, z
    while x != 1:
        x = mul[x, z]; o += 1
    assert o == d, (o, d)
    return q, add, mul, z

def build(p, f, k, d, e=1):
    q, add, mul, z = zeta(p, f, d, e)
    assert k % d == 0
    zp = [1]
    for j in range(1, k):
        zp.append(int(mul[zp[-1], z]))
    N = q * k
    T = np.empty((N, N), dtype=np.uint16)
    for j in range(k):
        for v in range(q):
            g = j * q + v
            # (v, j)(w, l) = (v + zeta^j w, j + l)
            img = mul[zp[j]]                      # zeta^j * w for all w
            sidx = add[v][img]                    # v + zeta^j w   (vector over w)
            for l in range(k):
                T[g, l * q:(l + 1) * q] = (((j + l) % k) * q + sidx).astype(np.uint16)
    return T

def check(T):
    N = T.shape[0]
    assert all(T[0, h] == h for h in range(N)) and all(T[g, 0] == g for g in range(N))
    for g in range(0, N, max(1, N // 40)):
        assert len(set(T[g].tolist())) == N
    # associativity sample
    rng = np.random.default_rng(1)
    for _ in range(2000):
        a, b, c = rng.integers(0, N, 3)
        assert T[T[a, b], c] == T[a, T[b, c]]
    return True

if __name__ == "__main__":
    if sys.argv[1] == "--info":
        p, f, k, d = map(int, sys.argv[2:6])
        print("N =", p ** f * k)
        sys.exit()
    p, f, k, d = map(int, sys.argv[1:5])
    out = sys.argv[5]
    e = int(sys.argv[6]) if len(sys.argv) > 6 else 1
    T = build(p, f, k, d, e)
    check(T)
    N = T.shape[0]
    with open(out, "wb") as fh:
        np.array([N], dtype=np.int32).tofile(fh)
        np.ascontiguousarray(T, dtype=np.uint16).tofile(fh)
    print(out, "N =", N)
