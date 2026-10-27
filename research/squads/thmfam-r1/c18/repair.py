#!/usr/bin/env python3
"""Extra generator lines (z=0, PGL matrices mod q) added to the LPS set psi(S_p).
Usage: repair.py p q VARIANT   (prints lines "a b c d 0")
VARIANT (letters are quaternions a0+a1 i+a2 j+a3 k, psi as in lps_haar.c; alpha = conjugation by psi(1+i+j+k)):
  f_1pijk   : psi(1+i+j+k)                      fixed by alpha, +1 letter
  f_ipjpk   : psi(i+j+k)                        fixed by alpha, +1 letter
  o_far     : {psi(i), psi(j), psi(k)}          alpha-orbit, +3 letters
  o_1i      : {psi(1+i), psi(1+j), psi(1+k)}    alpha-orbit, +3 letters
  o_2i      : {psi(2+i), psi(2+j), psi(2+k)}    alpha-orbit, +3 letters
  o_unip    : alpha-orbit of [[1,1],[0,1]], +3 letters
  o_unip_f  : f_1pijk + o_unip? (not used)
"""
import sys
p, q, var = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
# x^2+y^2 = -1 mod q, first (a,b) in lps_haar.c's search order
x = y = -1
for a in range(q):
    for b in range(q):
        if (a*a + b*b + 1) % q == 0:
            x, y = a, b; break
    if x >= 0: break
def psi(a0, a1, a2, a3):
    return [(a0 + a1*x + a3*y) % q, (-a1*y + a2 + a3*x) % q, (-a1*y - a2 + a3*x) % q, (a0 - a1*x - a3*y) % q]
def mul(X, Y):
    a, b, c, d = X; e, g, h, i = Y
    return [(a*e + b*h) % q, (a*g + b*i) % q, (c*e + d*h) % q, (c*g + d*i) % q]
def inv2(X):  # adjugate, a scalar multiple of the inverse (fine in PGL)
    a, b, c, d = X; return [d % q, (-b) % q, (-c) % q, a % q]
ALPHA = psi(1, 1, 1, 1)
def conj(X): return mul(mul(ALPHA, X), inv2(ALPHA))
def orbit(X):
    O = [X, conj(X), conj(conj(X))]
    return O
V = {
 'f_1pijk': [psi(1, 1, 1, 1)],
 'f_ipjpk': [psi(0, 1, 1, 1)],
 'o_far':   orbit(psi(0, 1, 0, 0)),
 'o_1i':    orbit(psi(1, 1, 0, 0)),
 'o_2i':    orbit(psi(2, 1, 0, 0)),
 'o_unip':  orbit([1, 1, 0, 1]),
 'o_u2':    orbit([1, 2, 0, 1]),
 'o_low':   orbit([1, 0, 1, 1]),
 'o_1p2i':  orbit(psi(1, 2, 0, 0)),
 'o_i2':    orbit(psi(0, 2, 0, 0)),
}
if var not in V:
    sys.exit('unknown variant ' + var)
for M in V[var]:
    print(*M, 0)
