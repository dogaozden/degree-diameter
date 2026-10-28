#!/usr/bin/env python3
"""Integer alpha-closed family in SL(2,Z), reduced mod q (PSL use).
alpha = conjugation by w = [[0,-1],[1,-1]] (w^3 = I over Z).
Usage: gen_int.py q m TOKEN...
  TOKEN = I | W | V   fixed letter (I, w, w^2)
  TOKEN = a:b:c:d     integer matrix X in SL(2,Z); contributes the 3-orbit {X, wXw^-1, w^2Xw^-2}
Prints lines "a b c d z" (z = 0). Deduplicates by PSL key (sign-identified) and checks size."""
import sys
q = int(sys.argv[1]); m = int(sys.argv[2]); toks = sys.argv[3:]
def mul(X, Y):
    a,b,c,d = X; e,g,h,i = Y; return (a*e+b*h, a*g+b*i, c*e+d*h, c*g+d*i)
w = (0,-1,1,-1); wi = (-1,1,-1,0); I = (1,0,0,1)
W2 = mul(w,w); V = W2
def conj(X): return mul(mul(w,X),wi)
def red(X): return tuple(t % q for t in X)
def key(X):
    X = red(X); lead = next(t for t in X if t)
    if lead > (q-1)//2: return tuple((-t) % q for t in X)
    return X
S = []; seen = set()
def add(X):
    k = key(X)
    if k in seen: raise SystemExit(f"collision/duplicate in PSL mod {q}: {X}")
    seen.add(k); S.append(red(X))
for t in toks:
    if t == 'I': add(I)
    elif t == 'W': add(w)
    elif t == 'V': add(W2)
    else:
        X = tuple(int(x) for x in t.split(':'))
        assert X[0]*X[3]-X[1]*X[2] == 1, "not in SL(2,Z)"
        O = [X, conj(X), conj(conj(X))]
        for Y in O: add(Y)
for X in S: print(*X, 0)
