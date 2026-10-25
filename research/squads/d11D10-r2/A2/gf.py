# GF(243) = GF(3)[x]/(x^5+2x+1) as in haar_sym.c (element = sum d_i 3^i, d_i = coefficient of x^i)
import sys
P, K = 3, 5
F = [1, 2, 0, 0, 0, 1]          # x^5 + 2x + 1, coefficients low -> high
Q = P ** K

def digits(a):
    return [(a // P**i) % P for i in range(K)]

def undig(d):
    return sum((d[i] % P) * P**i for i in range(K))

def _mul(a, b):
    da, db = digits(a), digits(b)
    pr = [0] * (2 * K - 1)
    for i in range(K):
        for j in range(K):
            pr[i + j] = (pr[i + j] + da[i] * db[j]) % P
    for i in range(2 * K - 2, K - 1, -1):
        t = pr[i]
        if t:
            for j in range(K + 1):
                pr[i - K + j] = (pr[i - K + j] - t * F[j]) % P
    return undig(pr[:K])

def _add(a, b):
    da, db = digits(a), digits(b)
    return undig([(da[i] + db[i]) % P for i in range(K)])

MUL = [[_mul(a, b) for b in range(Q)] for a in range(Q)]
ADD = [[_add(a, b) for b in range(Q)] for a in range(Q)]
NEG = [undig([(-d) % P for d in digits(a)]) for a in range(Q)]
INV = [0] * Q
for a in range(1, Q):
    for b in range(1, Q):
        if MUL[a][b] == 1:
            INV[a] = b
            break
for a in range(1, Q):
    assert INV[a], "field error"
SQ = set(MUL[a][a] for a in range(1, Q))   # nonzero squares

def poly_str(a):
    d = digits(a)
    terms = []
    for i in range(K - 1, -1, -1):
        if d[i]:
            c = d[i]
            mon = "" if i == 0 else ("x" if i == 1 else "x^%d" % i)
            terms.append((str(c) if (c != 1 or i == 0) else "") + mon)
    return "+".join(terms) if terms else "0"

def sub(a, b):
    return ADD[a][NEG[b]]

def mmul(X, Y):
    a1, b1, c1, d1 = X
    a2, b2, c2, d2 = Y
    return (ADD[MUL[a1][a2]][MUL[b1][c2]], ADD[MUL[a1][b2]][MUL[b1][d2]],
            ADD[MUL[c1][a2]][MUL[d1][c2]], ADD[MUL[c1][b2]][MUL[d1][d2]])

def pnorm(X):   # projective normal form in PSL(2,243): min of X and -X
    Y = tuple(NEG[v] for v in X)
    return min(X, Y)

def frob(X, j=1):   # entrywise x -> x^(3^j)
    out = []
    for v in X:
        for _ in range(j):
            w = 1
            for _ in range(P):
                w = MUL[w][v]
            v = w
        out.append(v)
    return tuple(out)

def pow_order(X, limit=100000):
    I = (1, 0, 0, 1)
    Y = X
    n = 1
    while pnorm(Y) != pnorm(I):
        Y = mmul(Y, X)
        n += 1
        if n > limit:
            return None
    return n

def trace(X):
    return ADD[X[0]][X[3]]

def det(X):
    return sub(MUL[X[0]][X[3]], MUL[X[1]][X[2]])

def in_gf3(a):
    return digits(a)[1:] == [0, 0, 0, 0]

def in_gf3_matrix(X):
    return all(in_gf3(v) for v in X)

def disc_class(X):   # 'unip' if tr = +-2, 'split' if tr^2-4 nonzero square, 'nonsplit' otherwise
    t = trace(X)
    D = sub(MUL[t][t], 4 % Q if False else ADD[1][ADD[1][ADD[1][1]]])
    if D == 0:
        return 'unip'
    return 'split' if D in SQ else 'nonsplit'

if __name__ == "__main__":
    # self-check: field axioms and Frobenius order 5
    import itertools, random
    for _ in range(2000):
        a, b, c = (random.randrange(Q) for _ in range(3))
        assert MUL[a][ADD[b][c]] == ADD[MUL[a][b]][MUL[a][c]]
    assert all(MUL[a][INV[a]] == 1 for a in range(1, Q))
    print("field ok; poly x^5+2x+1; |squares|", len(SQ))
    print("x^5 =", poly_str(_mul(digits(0)[0] or 3, 1)) if False else "check")
    print("frob order check:", all(frob((a, 0, 0, 1), 5)[0] == a for a in range(Q)))
