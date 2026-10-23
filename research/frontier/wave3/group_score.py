"""Small-order statistics of candidate groups G = M x Z_n (and products), to rank groups before searching.

Why: in a Haar graph H(G,S), an element s_i^-1 s_j of order k closes a 2k-cycle at every vertex (all vertices look
alike), and every such short cycle wastes words of length >= k.  Groups with many involutions (4-cycles) or elements
of order 3, 4 (6-, 8-cycles) cover fewer vertices within D.  Observed on (6,9) at N = 58,752 (60-180 s runs):
  SL(2,17) x Z12  f2 = 5e-5   solved in 0.4 s
  PSL(2,17) x Z24 f2 = 5e-3   best 6
  PGL(2,17) x Z12 f2 = 1e-2   best 7
  PSL(2,49)       f2 = 2e-2   best 23
  Z12 x| PGL(2,17) f2 = 3e-2  best 42
Score = sum_k f_k / (d-1)^(k-2) over k = 2..6, where f_k = fraction of elements of order exactly k.

  python3 group_score.py d SPEC... n        e.g.  python3 group_score.py 8 sl 17 12      (prints f2..f6, score)
Library: order_counts(spec) for 'sl q' / 'psl q' / 'pgl q' (exact class formulas), 'prod A B', 'cyc', and
score(d, counts).  meta / agl1 / tpgl / csl are not handled (use brute force if needed).
"""
import math
import sys
from collections import Counter


def factor_pp(q):
    p = next(t for t in range(2, q + 1) if q % t == 0)
    k, x = 0, q
    while x % p == 0:
        x //= p
        k += 1
    assert x == 1, "q must be a prime power"
    return p, k


def phi(n):
    r, x, t = n, n, 2
    while t * t <= x:
        if x % t == 0:
            while x % t == 0:
                x //= t
            r -= r // t
        t += 1
    if x > 1:
        r -= r // x
    return r


def divisors(n):
    return [t for t in range(1, n + 1) if n % t == 0]


def sl2_counts(q):
    """order -> number of elements of SL(2,q)"""
    p, _ = factor_pp(q)
    c = Counter()
    if p == 2:                       # SL = PSL = PGL
        c[1] += 1
        c[2] += q * q - 1
        for k in divisors(q - 1):
            if k > 1:
                c[k] += phi(k) // 2 * q * (q + 1)
        for k in divisors(q + 1):
            if k > 1:
                c[k] += phi(k) // 2 * q * (q - 1)
        return c
    c[1] += 1
    c[2] += 1
    c[p] += q * q - 1
    c[2 * p] += q * q - 1
    for k in divisors(q - 1):
        if k > 2:
            c[k] += phi(k) // 2 * q * (q + 1)
    for k in divisors(q + 1):
        if k > 2:
            c[k] += phi(k) // 2 * q * (q - 1)
    return c


def psl2_counts(q):
    p, _ = factor_pp(q)
    if p == 2:
        return sl2_counts(q)
    c = Counter()
    for k, v in sl2_counts(q).items():
        if k in (1, 2):
            c[1] += v                 # +-I -> e
        elif k == p or k == 2 * p:
            c[p] += v
        else:
            c[k // 2 if k % 2 == 0 else k] += v
    return Counter({k: v // 2 for k, v in c.items()})


def pgl2_counts(q):
    p, _ = factor_pp(q)
    if p == 2:
        return sl2_counts(q)
    c = Counter()
    c[1] += 1
    c[p] += q * q - 1
    c[2] += q * q                     # involutions: q(q+1)/2 split + q(q-1)/2 non-split
    for k in divisors(q - 1):
        if k > 2:
            c[k] += phi(k) // 2 * q * (q + 1)
    for k in divisors(q + 1):
        if k > 2:
            c[k] += phi(k) // 2 * q * (q - 1)
    return c


def cyc_counts(n):
    return Counter({k: phi(k) for k in divisors(n)})


def combine(c1, c2):
    out = Counter()
    for a, x in c1.items():
        for b, y in c2.items():
            out[a * b // math.gcd(a, b)] += x * y
    return out


def order_counts(tok, i=0):
    """parse a group spec (tokens) -> (Counter, next index)"""
    t = tok[i]
    if t in ("sl", "psl", "pgl"):
        q = int(tok[i + 1])
        j = i + 2
        if j < len(tok) and tok[j] == "poly":
            j += 2
        return {"sl": sl2_counts, "psl": psl2_counts, "pgl": pgl2_counts}[t](q), j
    if t == "prod":
        a, j = order_counts(tok, i + 1)
        b, j = order_counts(tok, j)
        return combine(a, b), j
    if t == "cyc":
        return Counter({1: 1}), i + 1
    raise ValueError("unsupported family " + t)


def group_counts(spec_tokens, n):
    c, j = order_counts(spec_tokens)
    assert j == len(spec_tokens)
    return combine(c, cyc_counts(n))


def score(d, counts, kmax=6):
    N = sum(counts.values())
    f = {k: counts.get(k, 0) / N for k in range(2, kmax + 1)}
    return sum(f[k] / (d - 1) ** (k - 2) for k in f), f, N


if __name__ == "__main__":
    d = int(sys.argv[1])
    toks = sys.argv[2:-1]
    n = int(sys.argv[-1])
    s, f, N = score(d, group_counts(toks, n))
    print(f"N={N} score={s:.3e} " + " ".join(f"f{k}={v:.2e}" for k, v in f.items()))
