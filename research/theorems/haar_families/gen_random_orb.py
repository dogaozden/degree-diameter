#!/usr/bin/env python3
"""Random alpha-closed S in SL(2,q) (use with --group psl or sl): alpha = conjugation by w = [[0,-1],[1,-1]] (order 3).
Usage: gen_random_orb.py q f norbits seed    f fixed letters from {I, w, w^2} (f <= 3), norbits random 3-orbits."""
import sys, random
q, f, k, seed = map(int, sys.argv[1:5]); R = random.Random(seed * 100003 + q)
def mul(X, Y):
    a,b,c,d = X; e,g,h,i = Y; return ((a*e+b*h) % q, (a*g+b*i) % q, (c*e+d*h) % q, (c*g+d*i) % q)
w = (0, q-1, 1, q-1); wi = (q-1, 1, q-1, 0)   # w^-1 = w^2
def conj(X): return mul(mul(w, X), wi)
def rand_sl():
    while True:
        a,b,c = R.randrange(q), R.randrange(q), R.randrange(q)
        if a: return (a, b, c, (1 + b*c) * pow(a, q-2, q) % q)
fixed = [(1,0,0,1), w, mul(w, w)][:f]
S = list(fixed)
def key(X): # PSL key
    a,b,c,d = X; lead = a if a else b
    return X if lead <= (q-1)//2 else tuple((-t) % q for t in X)
seen = {key(X) for X in S}
while len(S) < f + 3*k:
    X = rand_sl(); O = [X, conj(X), conj(conj(X))]
    ks = {key(Y) for Y in O}
    if len(ks) == 3 and not (ks & seen): S += O; seen |= ks
for X in S: print(*X, 0)
