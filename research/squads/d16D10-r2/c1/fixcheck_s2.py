# Independent coverage predicate for the c1 best S (validation against the EVAL-printed holes), then the
# alpha-fixed elements (x,0), x in C_PSL(g), checked directly. Odd side: words s1 s2^-1 ... s_m, m <= 9.
import re, sys, time
P = 31; N = 154571; RA = 56521
GM = (0, 30, 1, 12)
def normM(m):
    neg = tuple((-x) % P for x in m)
    return min(m, neg)
def mulM(m1, m2):
    a, b, c, d = m1; e, f, g, h = m2
    return ((a*e + b*g) % P, (a*f + b*h) % P, (c*e + d*g) % P, (c*f + d*h) % P)
def gmulA(x, y):
    return normM(mulM(x[:4], y[:4])) + ((x[4] + y[4]) % N,)
def gmulB(x, y):
    return normM(mulM(y[:4], x[:4])) + ((x[4] + y[4]) % N,)
def ginv(x):
    a, b, c, d, z = x
    return normM((d % P, (-b) % P, (-c) % P, a % P)) + ((-z) % N,)
ginvM = (12, (-30) % P, (-1) % P, 0)  # inverse of GM = (0,30,1,12) in SL(2,31)
def alphaE(x):
    a, b, c, d, z = x
    m = mulM(mulM(GM, (a, b, c, d)), ginvM)
    return normM(m) + ((RA * z) % N,)

S = []
for line in open('OUT_s2.txt.best'):
    m = re.search(r'mat\((\d+),(\d+),(\d+),(\d+)\) z=(\d+)', line)
    if m:
        t = tuple(int(m.group(i)) for i in range(1, 5))
        assert (t[0]*t[3] - t[1]*t[2]) % P == 1
        S.append(normM(t) + (int(m.group(5)),))
assert len(S) == 16, len(S)
assert (0, 0, 0, 0) != S[0] and S[0][:4] == (1, 0, 0, 1) and S[0][4] == 0
Sinv = [ginv(s) for s in S]

def build_L5(mult):
    cur = set(S)
    for letters in (Sinv, S, Sinv, S):
        cur = {mult(x, t) for x in cur for t in letters}
    return cur
def build_T4(mult):
    cur = set(Sinv)
    for letters in (S, Sinv, S):
        cur = {mult(x, t) for x in cur for t in letters}
    return cur

holes = []
for line in open('eval_s2.out'):
    m = re.match(r'uncovered (\d+) mat\((\d+),(\d+),(\d+),(\d+)\) z=(\d+)', line)
    if m:
        t = tuple(int(m.group(i)) for i in range(2, 6))
        holes.append(normM(t) + (int(m.group(6)),))
print("printed holes:", len(holes))

def cov_odd(h, mult, L5, T4):
    return any(mult(h, t) in L5 for t in T4)
def cov_even(h, mult, L5):
    return any(mult(h, t) in L5 for t in L5)

mult, L5, T4 = gmulA, build_L5(gmulA), build_T4(gmulA)
print("printed holes:", len(holes), "odd-side uncovered:", sum(1 for h in holes if not cov_odd(h, mult, L5, T4)))
T = set()
for a in range(P):
    for b in range(P):
        for c in range(P):
            for d in range(P):
                if (a*d - b*c) % P == 1:
                    X = (a, b, c, d)
                    if mulM(GM, X) == mulM(X, GM): T.add(normM(X))
fixed = [normM(x) + (0,) for x in sorted(T)]
st = [cov_odd(f, mult, L5, T4) for f in fixed]
print("C_PSL(g) classes:", len(T), "alpha-fixed (x,0) uncovered on odd side:", len(st) - sum(st))
