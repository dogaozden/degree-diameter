#!/usr/bin/env python3
"""c15 generator: alpha-closed S in PSL(2,q), alpha = conjugation by h, h of projective order k (k = 3, 5, 6).

h is the first companion matrix [[0,-1],[1,t]] (t = 0,1,2,... in F_q) whose projective order is exactly k.
Shapes:  1 -> S = {I} u O(x)   (Delta = k+1)      2 -> S = O(x) u O(y)  (Delta = 2k)
x, y: 'u' = [[1,1],[0,1]], 'l' = [[1,0],[1,1]], 'a' = [[2,1],[1,1]], 'b' = [[1,2],[0,1]], 'c' = [[2,1],[3,2]]
      or 'r' = random in PSL(2,q) (seeded by SEED and q).
Usage: gen_c15.py q k shape xname [xname2] [--seed SEED]   prints lines "a b c d 0" (mod q).
"""
import sys, random
args = sys.argv[1:]
seed = None
if '--seed' in args:
    i = args.index('--seed'); seed = int(args[i+1]); del args[i:i+2]
q, k, shape = int(args[0]), int(args[1]), int(args[2])
names = args[3:3+shape]
FIX = {'u': (1,1,0,1), 'l': (1,0,1,1), 'a': (2,1,1,1), 'b': (1,2,0,1), 'c': (2,1,3,2)}
I = (1,0,0,1)
def mul(X,Y):
    a,b,c,d = X; e,f,g,h = Y
    return ((a*e+b*g)%q, (a*f+b*h)%q, (c*e+d*g)%q, (c*f+d*h)%q)
def inv(X):
    a,b,c,d = X; return (d%q, (-b)%q, (-c)%q, a%q)
def neg(X): return tuple((-t)%q for t in X)
def key(X):
    a,b,c,d = X; lead = a % q if a % q else b % q
    return X if lead <= (q-1)//2 else neg(X)
def pord(X, maxo):
    Y = X
    for j in range(1, maxo+1):
        if Y == I or Y == neg(I): return j
        Y = mul(Y, X)
    return None
def find_h():
    for t in range(q):
        M = (0, q-1, 1, t)
        if pord(M, 2*k) == k: return M
    sys.exit(f"no element of projective order {k} in PSL(2,{q})")
h = find_h(); hi = inv(h)
def conj(X): return mul(mul(h, X), hi)
def orbit(X):
    O = [X]; Y = conj(X)
    while key(Y) != key(X):
        O.append(Y); Y = conj(Y)
        if len(O) > k: return None
    return O if len(O) == k else None
R = random.Random((seed or 0) * 1000003 + q)
def rand_sl():
    while True:
        a, b, c = R.randrange(q), R.randrange(q), R.randrange(q)
        if a: return (a, b, c, (1 + b*c) * pow(a, q-2, q) % q)
def pick(name):
    if name == 'r':
        while True:
            O = orbit(rand_sl())
            if O: return O
    X = FIX[name]
    O = orbit(X)
    if not O: sys.exit(f"fixed x={name} has orbit size != {k} under h mod {q}")
    return O
S = [I] if shape == 1 else []
seen = {key(X) for X in S}
for nm in names:
    O = pick(nm)
    while any(key(X) in seen for X in O):
        if nm != 'r': sys.exit(f"orbit of {nm} meets S")
        O = pick(nm)
    S += O; seen |= {key(X) for X in O}
assert len(S) == (k+1 if shape == 1 else 2*k), len(S)
for X in S: print(*X, 0)
