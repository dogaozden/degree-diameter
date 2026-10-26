"""Single-geodesic (SG) and far same-side pairs of a DM base, and whether sigma covers them (R: sigma-concurrency /
sigma^-1-collinearity).  usage: python3 sg.py in.txt"""
import sys, numpy as np
f = open(sys.argv[1]).read().split()
n, dg = int(f[0]), int(f[1]); V = 2 * n
ln = np.array(f[2:2 + n * dg], dtype=int).reshape(n, dg); sig = np.array(f[2 + n * dg:2 + n * dg + n], dtype=int)
I = np.zeros((n, n), dtype=np.int64)   # I[p, l]
for l in range(n): I[ln[l], l] = 1
PP = I @ I.T; LL = I.T @ I            # common lines / common points
P4 = PP @ PP; L4 = LL @ LL
S = np.zeros((n, n), dtype=np.int64); S[np.arange(n), sig] = 1   # S[p, sigma(p)]
# R for points: sigma(x), sigma(y) concurrent: LL[sig[x], sig[y]] > 0
Rp = LL[np.ix_(sig, sig)] > 0
sinv = np.argsort(sig); Rl = PP[np.ix_(sinv, sinv)] > 0
for name, A, A4, R in (("points", PP, P4, Rp), ("lines", LL, L4, Rl)):
    far = (A == 0); np.fill_diagonal(far, False)
    g4 = A4 - np.diag(np.diag(A4))
    # walks of length 4 between non-collinear distinct x, y are geodesics; subtract nothing else (A[x,y]=0)
    sgp = far & (g4 == 1); zp = far & (g4 == 0)
    print(name, "SG pairs", sgp.sum() // 2, "covered by R", (sgp & R).sum() // 2, "| distance>=6 pairs", zp.sum() // 2, "covered", (zp & R).sum() // 2)
    xs, ys = np.nonzero(np.triu(sgp & ~R)); print("  uncovered SG:", list(zip(xs.tolist(), ys.tolist()))[:10])
    deg = (sgp).sum(1); print("  SG degree histogram", np.bincount(deg)[:12].tolist())
