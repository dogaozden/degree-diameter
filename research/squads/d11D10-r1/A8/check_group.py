# Light check (no haar_sym): PSL(2,23) element orders and centralizer of an element of order 11; Z_12409 facts.
p = 23
def mul(A, B):
    a, b, c, d = A; e, f, g, h = B
    return ((a*e + b*g) % p, (a*f + b*h) % p, (c*e + d*g) % p, (c*f + d*h) % p)
def norm(A):  # projective normalisation: first nonzero entry in {1..(p-1)/2} (PSL = SL / {+-1})
    for x in A:
        if x % p:
            s = 1 if x % p <= (p - 1) // 2 else -1
            return tuple((s * y) % p for y in A) if s == 1 else tuple((-y) % p for y in A)
    raise ValueError
SL = [(a, b, c, d) for a in range(p) for b in range(p) for c in range(p) for d in range(p) if (a*d - b*c) % p == 1]
PSL = sorted({norm(A) for A in SL})
I = norm((1, 0, 0, 1))
def order(A):
    k, X = 1, A
    while norm(X) != I:
        X = norm(mul(X, A)); k += 1
    return k
from collections import Counter
print("|SL|=", len(SL), " |PSL|=", len(PSL))
print("element-order histogram:", sorted(Counter(order(A) for A in PSL).items()))
g = next(A for A in PSL if order(A) == 11)
cent = [x for x in PSL if norm(mul(g, x)) == norm(mul(x, g))]
print("centralizer of an order-11 element has", len(cent), "elements (PSL)")
def f(n):
    d = 2; out = {}
    while d * d <= n:
        while n % d == 0: out[d] = out.get(d, 0) + 1; n //= d
        d += 1
    if n > 1: out[n] = out.get(n, 0) + 1
    return out
print("12409 =", f(12409), " 12408 =", f(12408), " 12408/11 =", 12408 // 11)
print("N = |PSL(2,23)| * 12409 =", len(PSL) * 12409, " vertices =", 2 * len(PSL) * 12409)
