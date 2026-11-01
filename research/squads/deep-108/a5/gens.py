# gens.py: A5 inside PSL(2,p) (p = +-1 mod 10), an element r of order 5 in A5, an involution t in A5 inverting r,
# and the involution s of PSL(2,p) commuting with r. Prints matrices as "a b c d" (entries mod p).
import sys, itertools, random
p = int(sys.argv[1]) if len(sys.argv) > 1 else 59
def mul(x, y): return ((x[0]*y[0]+x[1]*y[2]) % p, (x[0]*y[1]+x[1]*y[3]) % p, (x[2]*y[0]+x[3]*y[2]) % p, (x[2]*y[1]+x[3]*y[3]) % p)
def norm(x):
    a, b, c, d = x
    if a == 0: return x if b <= (p-1)//2 else tuple((-v) % p for v in x)
    return x if a <= (p-1)//2 else tuple((-v) % p for v in x)
I = (1, 0, 0, 1)
def order(x):
    y = x; k = 1
    while norm(y) != I: y = mul(y, x); k += 1
    return k
def closure(gens):
    S = {I}; fr = [I]
    while fr:
        nf = []
        for x in fr:
            for g in gens:
                y = norm(mul(x, g))
                if y not in S: S.add(y); nf.append(y)
        fr = nf
        if len(S) > 1000: return S
    return S
random.seed(1)
def rnd_sl():
    while True:
        a, b, c = (random.randrange(p) for _ in range(3))
        if a: return (a, b, c, (1 + b*c) * pow(a, p-2, p) % p)
while True:
    a = rnd_sl(); b = rnd_sl()
    if order(a) == 2 and order(b) == 3 and order(mul(a, b)) == 5:
        A = closure([a, b])
        if len(A) == 60: break
r = next(x for x in A if order(x) == 5)
inv = lambda x: (x[3], (-x[1]) % p, (-x[2]) % p, x[0])
t = next(x for x in A if order(x) == 2 and norm(mul(mul(x, r), x)) == norm(inv(r)))
# s: involution commuting with r (search all of SL(2,p))
s = None
for a_ in range(p):
    for b_ in range(p):
        for c_ in range(p):
            if a_ == 0: continue
            x = (a_, b_, c_, (1 + b_*c_) * pow(a_, p-2, p) % p)
            if norm(mul(x, r)) == norm(mul(r, x)) and order(x) == 2: s = x; break
        if s: break
    if s: break
r2 = norm(mul(r, r))
f = lambda x: " ".join(map(str, norm(x)))
print("A_gens", f(a), f(b)); print("r", f(r)); print("r2", f(r2)); print("t", f(t)); print("s", f(s))
