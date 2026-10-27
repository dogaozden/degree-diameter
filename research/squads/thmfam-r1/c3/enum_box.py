#!/usr/bin/env python3
"""Enumerate SL(2,Z) matrices with entries in [-2,2] and group them into alpha-orbit classes over Z (sign-identified)."""
import itertools, json
def mul(X, Y):
    a,b,c,d = X; e,g,h,i = Y; return (a*e+b*h, a*g+b*i, c*e+d*h, c*g+d*i)
w = (0,-1,1,-1); wi = (-1,1,-1,0)
def conj(X): return mul(mul(w,X),wi)
def pk(X): return X if next(t for t in X if t) > 0 else tuple(-t for t in X)
box = [X for X in itertools.product(range(-2,3), repeat=4) if X[0]*X[3]-X[1]*X[2] == 1]
classes = {}
for X in box:
    O = [X, conj(X), conj(conj(X))]
    if len({pk(Y) for Y in O}) < 3: continue           # fixed by alpha up to sign (I, w, w^2 and -those)
    k = frozenset(pk(Y) for Y in O)
    classes.setdefault(k, X)
print(len(box), "box SL2(Z) elements;", len(classes), "3-orbit classes (sign-identified) with a box rep")
json.dump([list(v) for v in classes.values()], open('orbit_reps.json','w'))
