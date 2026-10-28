#!/usr/bin/env python3
"""c11: uniform non-liftable alpha-closed families in SL(2,q) (use with --group psl), alpha = conj by w = [[0,-1],[1,-1]].
Usage: gen_c11.py q m VARIANT DELTA      VARIANT in 1..15, DELTA in {6, 8}
  DELTA 6: S = O(X) u O(Y)                      (type 3+3)
  DELTA 8: S = {I, w} u O(X) u O(Y)             (type 1+1+3+3)
X, Y are formulas in q built from t = g^k (g = least primitive root mod q, k per variant): powers t^e, t^h with
h = (q+1)/2, constants 2,3,5, the trace (companion matrices [[0,-1],[1,tau]] with tau = t^n + t^-n, the Dickson
polynomial D_n(t + 1/t)), and the Legendre sign L = t^((q-1)/2) = +-1.
Prints one line "a b c d 0" per generator. Exits 3 (no output) if the family is degenerate (orbit size != 3 or
Delta mismatch), so family_score reports an error row instead of a wrong score."""
import sys

q, m, V, D = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
half = (q - 1) // 2

def least_prim_root(p):
    fac = [f for f in range(2, p) if (p - 1) % f == 0 and all(f % d for d in range(2, int(f**.5) + 1))]
    for g in range(2, p):
        if all(pow(g, (p - 1) // f, p) != 1 for f in fac):
            return g
    raise ValueError

def mul(X, Y):
    a, b, c, d = X; e, g_, h, i = Y
    return ((a*e + b*h) % q, (a*g_ + b*i) % q, (c*e + d*h) % q, (c*g_ + d*i) % q)

w = (0, q - 1, 1, q - 1); wi = mul(w, w)            # w^-1 = w^2
I = (1, 0, 0, 1)
def conj(X): return mul(mul(w, X), wi)
def orbit(X): return [X, conj(X), conj(conj(X))]
def key(X):
    a, b, c, d = X; lead = a if a else b
    return X if lead <= half else tuple((-x) % q for x in X)

# ---- variant parameters -------------------------------------------------------------------------------------------
# k: t = g^k.  Each entry spec is ('M', a, b, c) (matrix with a,b,c given as exponents of t, or ('c', constant)),
# or ('C', n) (companion matrix with trace t^n + t^-n), ('C2', n) (trace 2 + ...).
# Exponent tokens: an int e means t^e; 'h' means t^((q+1)/2); 'L' means the Legendre sign (+-1).
VARIANTS = {
    1:  dict(k=1, X=('M', ('t', 1), ('t', 3), ('t', 0)),   Y=('M', ('t', -1), ('t', 1), ('t', 0))),
    2:  dict(k=1, X=('M', ('t', 1), ('t', 0), ('t', 3)),   Y=('M', ('t', -1), ('t', -1), ('t', 0))),
    3:  dict(k=1, X=('M', ('t', 1), ('t', 3), ('t', 'h')), Y=('M', ('t', 2), ('t', 0), ('t', -1))),
    4:  dict(k=1, X=('C', 1), Y=('C', 3)),
    5:  dict(k=1, X=('C', 2), Y=('C', 5)),
    6:  dict(k=1, X=('C', 3), Y=('M', ('t', 1), ('t', -3), ('t', 'h'))),
    7:  dict(k=1, X=('M', ('c', 2), ('t', 1), ('t', 0)),   Y=('M', ('t', -1), ('c', 2), ('t', -1))),
    8:  dict(k=1, X=('M', ('t', 1), ('L', 0), ('t', 2)),   Y=('M', ('t', 3), ('c', 2), ('t', -1))),
    9:  dict(k=1, X=('M', ('c', 2), ('c', 3), ('t', 1)),   Y=('M', ('t', -1), ('c', 5), ('t', 0))),
    10: dict(k=2, X=('M', ('t', 1), ('t', 3), ('t', 0)),   Y=('M', ('t', -1), ('t', 1), ('t', 0))),
    11: dict(k=1, X=('M', ('t', 'h'), ('t', 3), ('t', -1)), Y=('M', ('t', '-h'), ('t', -3), ('t', 1))),
    12: dict(k=1, X=('C', 'h'), Y=('C', 1)),
    13: dict(k=1, X=('C', 1), Y=('M', ('t', 'h'), ('t', -2), ('t', 0))),
    14: dict(k=1, X=('M', ('t', 3), ('t', 1), ('t', -1)), Y=('C', 2)),
    15: dict(k=1, X=('C2', 1), Y=('C2', 3)),
}
if V not in VARIANTS:
    sys.exit(2)
P = VARIANTS[V]
g = least_prim_root(q)
t = pow(g, P['k'], q)
tinv = pow(t, q - 2, q)
h = (q + 1) // 2
L = 1 if pow(t, half, q) == 1 else q - 1            # Legendre sign of t as an element of F_q (1 or -1)

def tp(e):
    if e == 'h': return pow(t, h, q)
    if e == '-h': return pow(t, (-h) % (q - 1), q)
    if e == 0: return 1
    return pow(t, e % (q - 1), q)

def val(spec):
    kind = spec[0]
    if kind == 't': return tp(spec[1])
    if kind == 'c': return spec[1] % q
    if kind == 'L': return L
    raise ValueError(kind)

def M(a, b, c):
    a_, b_, c_ = a, b, c
    if a_ % q == 0: raise ValueError('a=0')
    d = (1 + b_ * c_) * pow(a_, q - 2, q) % q
    return (a_ % q, b_ % q, c_ % q, d)

def build(spec):
    if spec[0] == 'M':
        return M(*[val(s) for s in spec[1:]])
    if spec[0] == 'C':
        n = spec[1]
        tau = (tp(n) + tp(-n if n != 'h' else '-h')) % q if n != 'h' else (tp('h') + tp('-h')) % q
        return (0, q - 1, 1, tau)
    if spec[0] == 'C2':
        n = spec[1]
        tau = (2 + tp(n) + tp(-n)) % q
        return (0, q - 1, 1, tau)
    raise ValueError(spec[0])

X = build(P['X']); Y = build(P['Y'])
S = []
seen = set()
def add_orbit(Z):
    O = orbit(Z)
    if len({key(x) for x in O}) != 3:
        sys.stderr.write(f'degenerate orbit (size<3) for {Z} at q={q}\n'); sys.exit(3)
    for x in O:
        k_ = key(x)
        if k_ in seen:
            sys.stderr.write(f'overlap at q={q}\n'); sys.exit(3)
        seen.add(k_); S.append(x)

if D == 8:
    for f in (I, w):
        seen.add(key(f)); S.append(f)
add_orbit(X); add_orbit(Y)
if len(S) != D:
    sys.stderr.write(f'Delta {len(S)} != {D}\n'); sys.exit(3)
for x in S:
    print(*x, 0)
