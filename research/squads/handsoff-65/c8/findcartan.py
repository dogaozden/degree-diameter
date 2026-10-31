from g2lie import *
random.seed(7)
Gm = [mat(v) for v in G2basis]
best = None
for trial in range(400):
    c = [random.randrange(p) for _ in range(14)]
    X = lincomb(c, Gm)
    A = adm(X)
    tot = 0; dims = {}
    for lam in range(p):
        B = [[(A[i][j] - (lam if i == j else 0)) % p for j in range(14)] for i in range(14)]
        d = 14 - rank(B)
        dims[lam] = d; tot += d
    if tot == 14:
        print("trial", trial, "eigen dims", dims)
        if dims[0] == 2 and max(dims[l] for l in range(1, 5)) <= 2:
            best = (c, dims); break
print("best", best)
import pickle
pickle.dump(best, open("cartan.pkl", "wb"))
