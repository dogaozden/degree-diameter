from lin import *
random.seed(1)
ok = 0; tries = 0; fails = 0
for t in range(40):
    c = [random.randrange(p) for _ in G2basis]
    X = [[0]*N for _ in range(N)]
    for ci, v in zip(c, G2basis):
        if ci:
            M = mat(v)
            X = madd(X, [[ci*x % p for x in r] for r in M])
    I = ident()
    IpX = madd(I, X); ImX = madd(I, X, -1)
    if all(all(x == 0 for x in r) for r in [[0]*N]) : pass
    try:
        g = mm(ImX, minv(IpX))
    except StopIteration:
        fails += 1; continue
    tries += 1
    if preserves_phi(g): ok += 1
print("cayley: tries", tries, "preserve phi", ok, "noninv", fails)
