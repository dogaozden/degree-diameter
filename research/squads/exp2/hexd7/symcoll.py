import random, itertools
p = 11
def mul(A, B): return ((A[0]*B[0]+A[1]*B[2]) % p, (A[0]*B[1]+A[1]*B[3]) % p, (A[2]*B[0]+A[3]*B[2]) % p, (A[2]*B[1]+A[3]*B[3]) % p)
def inv(A): return (A[3] % p, (-A[1]) % p, (-A[2]) % p, A[0] % p)
def det(A): return (A[0]*A[3]-A[1]*A[2]) % p
I = (1, 0, 0, 1)
SL = [(a, b, c, d) for a in range(p) for b in range(p) for c in range(p) for d in range(p) if (a*d-b*c) % p == 1]
SYM = [A for A in SL if A[1] == A[2]]
def T(A): return (A[0], A[2], A[1], A[3])
negI = (p-1, 0, 0, p-1)
def cen(A): return A in (I, negI)
# orthogonal g of order 3 mod +-I
G = [g for g in SL if mul(T(g), g) == I and not cen(g) and not cen(mul(g, g)) and cen(mul(mul(g, g), g))]
g = G[0]; gi = inv(g)
al = lambda x: mul(mul(g, x), gi)
def orbit(x): return [x, al(x), al(al(x))]
rng = random.Random(1)
def count(sym):
    pool = SYM if sym else SL
    x, y = rng.choice(pool), rng.choice(pool)
    S = [I] + orbit(x) + orbit(y)
    if len(set(S)) < 7: return None
    w2 = set(mul(inv(a), b) for a in S for b in S if a != b)
    w2pairs = [(i, j) for i in range(7) for j in range(7) if i != j]
    from collections import Counter
    c = Counter(mul(inv(S[i]), S[j]) for i, j in w2pairs)
    coll = [(k, [(i, j) for i, j in w2pairs if mul(inv(S[i]), S[j]) == k]) for k, v in c.items() if v > 1]
    return len(w2), coll
for sym in (0, 1):
    res = [count(sym) for _ in range(200)]
    res = [r for r in res if r]
    print('sym', sym, 'mean distinct length-2 words (of 42):', sum(r[0] for r in res) / len(res), 'samples with collisions:', sum(1 for r in res if r[1]))
    ex = next((r for r in res if r[1]), None)
    if ex: print('  example collisions (slot pairs i,j for s_i^-1 s_j; slot 0 = e, 1-3 orbit x, 4-6 orbit y):', ex[1][:4])
print('--- with Z_7 factor, z -> 2z, S = {e} + 2 orbits; distinct elements of (S^-1 S)^j, j = 1, 2')
n, r = 7, 2
def gm(X, Y): return (mul(X[0], Y[0]), (X[1] + Y[1]) % n)
def ginvz(X): return (inv(X[0]), (-X[1]) % n)
def alz(X): return (al(X[0]), (r * X[1]) % n)
def orbz(X): return [X, alz(X), alz(alz(X))]
def levels(S):
    W1 = set(gm(ginvz(a), b) for a in S for b in S)
    W2 = set(gm(u, v) for u in W1 for v in W1)
    return len(W1), len(W2)
for sym in (0, 1):
    pool = SYM if sym else SL
    out = []
    for _ in range(40):
        x = (rng.choice(pool), rng.randrange(n)); y = (rng.choice(pool), rng.randrange(n))
        S = [(I, 0)] + orbz(x) + orbz(y)
        if len(set(S)) < 7: continue
        out.append(levels(S))
    out.sort()
    print('sym', sym, 'min/median/max of |(S^-1S)^2|:', out[0], out[len(out)//2], out[-1])
