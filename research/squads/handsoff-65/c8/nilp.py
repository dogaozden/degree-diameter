from g2lie import *
import pickle
random.seed(11)
Gm = [mat(v) for v in G2basis]
def mpow(A, k):
    R = ident()
    for _ in range(k): R = mm(R, A)
    return R
def iszero(A): return all(x == 0 for r in A for x in r)
found = []
tries = 0
for trial in range(300):
    c = [random.randrange(p) for _ in range(14)]
    X = lincomb(c, Gm)
    A = adm(X)
    dims = {}; tot = 0; spaces = {}
    for lam in range(p):
        B = [[(A[i][j] - (lam if i == j else 0)) % p for j in range(14)] for i in range(14)]
        ns = nullspace(B, 14)
        dims[lam] = len(ns); tot += len(ns); spaces[lam] = ns
    if tot != 14 or dims[0] < 2: continue
    for lam in range(1, p):
        E = spaces[lam]
        if not E: continue
        for s in range(60):
            cc = [random.randrange(p) for _ in E]
            v = [sum(cc[k] * E[k][i] for k in range(len(E))) % p for i in range(14)]
            if not any(v): continue
            e = lincomb(v, Gm)
            tries += 1
            if iszero(mpow(e, 3)) and not iszero(e):
                found.append((trial, lam, e))
    if len(found) >= 40: break
print("trials", trial, "nilpotent e with e^3=0 found:", len(found), "samples", tries)
pickle.dump([(f[0], f[1], f[2]) for f in found], open("nilp.pkl", "wb"))
ok = 0
for t, lam, e in found[:20]:
    x = madd(ident(), e); x = madd(x, [[ (2*y) % p for y in r] for r in mm(e, e)], 1)  # placeholder
for t, lam, e in found[:10]:
    e2 = mm(e, e)
    inv2 = pow(2, p-2, p)
    for tt in [1, 2, 3, 4]:
        g = madd(ident(), [[tt*x % p for x in r] for r in e])
        g = madd(g, [[(tt*tt*inv2*x) % p for x in r] for r in e2])
        if preserves_phi(g): ok += 1
print("exp(te) preserving phi:", ok, "of", 40)
