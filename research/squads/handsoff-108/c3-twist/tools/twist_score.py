"""Element-order densities f_k (k = 2..6) of G = Z_n x| PGL(2,q) (tpgl q, odd prime q), by brute force over PGL,
and the group_score score sum_k f_k/(d-1)^(k-2) (uses research/frontier/wave3/group_score.py).
Order of (g,z): with chi(g) = +1, (g,z)^m = (g^m, m z); with chi(g) = -1, (g,z)^m = (g^m, z [m odd]*...)."""
import sys
from math import gcd
from collections import Counter
sys.path.insert(0, "/home/user/degree-diameter/research/frontier/wave3")
from group_score import score

def lcm(a, b):
    return a * b // gcd(a, b)

def pgl_elements(q):
    seen, out = set(), []
    for a in range(q):
        for b in range(q):
            for c in range(q):
                for d in range(q):
                    if (a * d - b * c) % q == 0:
                        continue
                    # normalise mod scalars: first nonzero entry equal to 1
                    t = next(x for x in (a, b, c, d) if x)
                    inv = pow(t, q - 2, q)
                    key = tuple(x * inv % q for x in (a, b, c, d))
                    if key not in seen:
                        seen.add(key); out.append(key)
    return out

def mul(A, B, q):
    a, b, c, d = A; e, f, g, h = B
    return ((a * e + b * g) % q, (a * f + b * h) % q, (c * e + d * g) % q, (c * f + d * h) % q)

def norm(M, q):
    t = next(x for x in M if x)
    inv = pow(t, q - 2, q)
    return tuple(x * inv % q for x in M)

def pgl_order_chi(q):
    res = []
    issq = {v * v % q for v in range(1, q)}
    for M in pgl_elements(q):
        det = (M[0] * M[3] - M[1] * M[2]) % q
        chi = 1 if det in issq else -1
        I = norm((1, 0, 0, 1), q); X = M; o = 1
        while norm(X, q) != I:
            X = norm(mul(X, M, q), q); o += 1
        res.append((o, chi))
    return res

def tpgl_counts(q, n):
    cnt = Counter(); total = 0
    for og, chi in pgl_order_chi(q):
        for z in range(n):
            if chi == 1:
                o = lcm(og, n // gcd(z, n))
            else:
                if z == 0:
                    o = og
                else:
                    o = og if og % 2 == 0 else 2 * og
            cnt[o] += 1; total += 1
    return {k: cnt[k] / total for k in range(1, 7)}, total

if __name__ == "__main__":
    q, n = int(sys.argv[1]), int(sys.argv[2])
    f, tot = tpgl_counts(q, n)
    print("tpgl %d x Z_%d  |G| = %d" % (q, n, tot))
    print("f2..f6 =", ["%.2e" % f[k] for k in range(2, 7)], " involution count =", round(f[2] * tot))
    print("score (d=10) =", score(10, {k: f[k] for k in range(1, 7)}))
