# Hoffman (ratio) bound for pairwise non-orthogonal sets inside one square class of E_q (points with N(a) = x0^2 + x3^2
# a square, resp. a non-square). Usage: python3 hoffman.py q C
import sys, time
import numpy as np
q, C = int(sys.argv[1]), int(sys.argv[2])
rows = np.loadtxt(f'/home/user/degree-diameter/research/cell147/data/E{q}.map', dtype=np.int64)
X = rows[:, 2:9] % q
sq = {x * x % q for x in range(1, q)}
nA = (C * X[:, 0] ** 2 + X[:, 3] ** 2) % q          # = -Q_A = Q4
for name, sel in (('square', np.isin(nA, list(sq))), ('nonsquare', ~np.isin(nA, list(sq)) & (nA != 0)), ('a=0', nA == 0)):
    Y = X[sel]; n = len(Y)
    if n == 0: continue
    B = (np.outer(Y[:, 0], Y[:, 4]) + np.outer(Y[:, 4], Y[:, 0]) + np.outer(Y[:, 1], Y[:, 5]) + np.outer(Y[:, 5], Y[:, 1])
         + np.outer(Y[:, 2], Y[:, 6]) + np.outer(Y[:, 6], Y[:, 2]) - 2 * np.outer(Y[:, 3], Y[:, 3])) % q
    Adj = (B == 0).astype(np.float64); np.fill_diagonal(Adj, 0)
    deg = Adj.sum(axis=1)
    t0 = time.time(); ev = np.linalg.eigvalsh(Adj)
    k = deg.max(); lmin = ev[0]
    print(f"{name}: n={n} degree {deg.min():.0f}..{deg.max():.0f} lambda_min={lmin:.4f} Hoffman bound {n * (-lmin) / (k - lmin):.2f} ({time.time()-t0:.0f}s)", flush=True)
    del Adj, B
