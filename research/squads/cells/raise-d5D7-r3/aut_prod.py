"""aut_prod.py: order-3 automorphisms of G = H x Z (|Z| = b cyclic-or-abelian, central; |H| = a coprime to b)
of the form alpha(x) = c_g(pi_H x) * (pi_Z x)^r, where c_g is conjugation by g in H (g^3 = 1) and r^3 = 1 mod b.
Fix(alpha) = C_H(g) x Fix(r on Z).  The record's diagnostic is |Fix| = 6 (N = 1560: S5 x Z13, g a 3-cycle, r = 3).

usage: python3 -I aut_prod.py GROUPFILE B R OUTPREFIX
  B = order of the central Hall factor Z (must divide |G| with gcd(B, |G|/B) = 1); R = multiplier r (r^3 = 1 mod B).
Writes OUTPREFIX_<k>.txt for the order-3 element g of H with the smallest |Fix| (k = 0 is the best) and prints all.
"""
import sys
from math import gcd


def load(p):
    with open(p) as f:
        m = int(f.readline())
        T = [list(map(int, f.readline().split())) for _ in range(m)]
    return m, T


def main(gp, B, R, prefix):
    n, T = load(gp)
    A = n // B
    assert A * B == n and gcd(A, B) == 1, "B must be a Hall factor"
    inv = [next(y for y in range(n) if T[x][y] == 0) for x in range(n)]

    def power(x, k):
        y = 0
        for _ in range(k):
            y = T[y][x]
        return y
    # exponent tables for the Hall projections (fast powers via repeated squaring on the table)
    def pw(x, k):
        res, base = 0, x
        while k:
            if k & 1:
                res = T[res][base]
            base = T[base][base]
            k >>= 1
        return res
    u = next(k for k in range(n) if k % A == 1 % A and k % B == 0)   # pi_H(x) = x^u
    v = next(k for k in range(n) if k % A == 0 and k % B == 1 % B)   # pi_Z(x) = x^v
    piH = [pw(x, u) for x in range(n)]
    piZ = [pw(x, v) for x in range(n)]
    for x in range(n):
        assert T[piH[x]][piZ[x]] == x, "decomposition failed"
    Hset = [x for x in range(n) if piZ[x] == 0]
    Zset = [x for x in range(n) if piH[x] == 0]
    assert len(Hset) == A and len(Zset) == B
    order3 = [g for g in Hset if g != 0 and T[g][T[g][g]] == 0]
    if R % B != 1 % B:
        assert pow(R, 3, B) == 1 % B, "R^3 != 1 mod B"
    results = []
    seen = set()
    for g in order3:
        if g in seen:
            continue
        cls = {T[T[x][g]][inv[x]] for x in Hset}
        seen |= cls
        gi = inv[g]
        alpha = []
        for x in range(n):
            h = T[T[g][piH[x]]][gi]           # g h g^-1
            alpha.append(T[h][pw(piZ[x], R)])
        if len(set(alpha)) != n:
            continue
        fix = sum(1 for x in range(n) if alpha[x] == x)
        # automorphism check on random pairs
        import random
        random.seed(7)
        for _ in range(3000):
            x, y = random.randrange(n), random.randrange(n)
            assert alpha[T[x][y]] == T[alpha[x]][alpha[y]], "not a homomorphism"
        results.append((fix, g, alpha))
    results.sort(key=lambda t: t[0])
    for k, (fix, g, alpha) in enumerate(results):
        path = f"{prefix}_{k}.txt"
        with open(path, "w") as f:
            f.write(" ".join(map(str, alpha)) + "\n")
        print(f"class {k}: g={g} |Fix|={fix} 3-orbits={(n - fix) // 3} -> {path}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]))
