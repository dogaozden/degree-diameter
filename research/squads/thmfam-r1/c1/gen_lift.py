#!/usr/bin/env python3
"""Integer-lift family, Delta = 6, type 3+3: S = O(X) u O(Y) in SL(2,q), group psl.
O(M) = {M, w M w^-1, w^2 M w^-2}, w = [[0,-1],[1,-1]] (order 3 in SL(2,Z)).
Usage: gen_lift.py q m x1 x2 x3 x4 y1 y2 y3 y4   (X = [[x1,x2],[x3,x4]], Y = [[y1,y2],[y3,y4]], integers, det 1)
m is ignored (psl, z = 0). Prints the 6 lines "a b c d 0"; exits 1 if the 6 elements are not distinct in PSL(2,q)."""
import sys
q = int(sys.argv[1]); X = tuple(int(t) for t in sys.argv[3:7]); Y = tuple(int(t) for t in sys.argv[7:11])
def mul(A, B):
    a,b,c,d = A; e,g,h,i = B
    return (a*e+b*h, a*g+b*i, c*e+d*h, c*g+d*i)
w = (0, -1, 1, -1); wi = (-1, 1, -1, 0)           # w^-1 = w^2
def conj(M): return mul(mul(w, M), wi)          # alpha(M) = w M w^-1
def orbit(M): return [M, conj(M), conj(conj(M))]   # w^2 M w^-2 = alpha(alpha(M))
def red(M): return tuple(t % q for t in M)
def pkey(M):                                    # PSL key: identify M with -M
    M = red(M); lead = next(t for t in M if t)
    return M if lead <= (q-1)//2 else tuple((-t) % q for t in M)
S = orbit(X) + orbit(Y)
keys = [pkey(M) for M in S]
if len(set(keys)) != 6:
    print("NOT_DISTINCT", file=sys.stderr); sys.exit(1)
for M in S:
    print(*red(M), 0)
