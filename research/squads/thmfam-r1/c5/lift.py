#!/usr/bin/env python3
"""Lift each generator "a b c d z" (matrix mod p, det 1 mod p) to an integer matrix with det exactly 1 and small entries.
usage: lift.py p GENS_FILE OUT_FILE   (GENS_FILE: lines 'a b c d z'; output lines 'A B C D z')
For psl the lift may be any sign of the class; for sl the lift must be congruent to the given matrix exactly."""
import sys, math
def egcd(a, b):
    if b == 0: return (a, 1, 0) if a >= 0 else (-a, -1, 0)
    g, x, y = egcd(b, a % b)
    return g, y, x - (a // b) * y
def lift(p, a, b, c, d, sign_ok):
    best = None
    targets = [(a, b, c, d)] + ([((-a) % p, (-b) % p, (-c) % p, (-d) % p)] if sign_ok else [])
    for (A0, B0, C0, D0) in targets:
        for ka in range(-3, 4):
            A = A0 + ka * p
            for kc in range(-3, 4):
                C = C0 + kc * p
                if math.gcd(A, C) != 1: continue
                g, x, y = egcd(A, C)            # A*x + C*y = g = +-1
                if g < 0: x, y = -x, -y
                # general solution with det 1: b = -y + t*A, d = x + t*C
                for t in range(-6 * p, 6 * p + 1):
                    b = -y + t * A; dd = x + t * C
                    if b % p == B0 % p and dd % p == D0 % p:
                        cand = (A, b, C, dd)
                        assert A * dd - b * C == 1
                        if best is None or max(map(abs, cand)) < max(map(abs, best)): best = cand
    return best
if __name__ == '__main__':
    p = int(sys.argv[1]); sign_ok = sys.argv[4] == 'psl' if len(sys.argv) > 4 else False
    out = []
    for line in open(sys.argv[2]):
        if not line.strip(): continue
        a, b, c, d, z = map(int, line.split())
        L = lift(p, a, b, c, d, sign_ok)
        assert L is not None, (a, b, c, d)
        out.append("%d %d %d %d %d" % (L[0], L[1], L[2], L[3], z))
    open(sys.argv[3], 'w').write("\n".join(out) + "\n")
    print("\n".join(out))
