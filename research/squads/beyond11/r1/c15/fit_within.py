# Logistic model of P(solved within E evals | ln mu [, ln(start+1), D]) using conditional labels:
# a run contributes label 1 if solved with evals <= E, label 0 if (unsolved or solved later) with evals >= E,
# and is dropped if it stopped before E without solving (no information at E).
import math, sys
exec(open('/home/user/degree-diameter/research/squads/beyond11/r1/c15/analyze.py').read().split('print("unique runs')[0])
k3r = [x for x in rows if x["k"] == 3]
def solve_lr(X, y, iters=50, lam=1e-3):
    p = len(X[0]); beta = [0.0] * p
    for _ in range(iters):
        g = [0.0] * p; H = [[0.0] * p for _ in range(p)]
        for xi, yi in zip(X, y):
            z = sum(b * v for b, v in zip(beta, xi)); pr = 1 / (1 + math.exp(-max(-30, min(30, z))))
            for a in range(p):
                g[a] += (yi - pr) * xi[a]
                for c in range(p): H[a][c] += pr * (1 - pr) * xi[a] * xi[c]
        for a in range(p): g[a] -= lam * beta[a]; H[a][a] += lam
        M = [row[:] + [g[i]] for i, row in enumerate(H)]
        for i in range(p):
            piv = max(range(i, p), key=lambda r: abs(M[r][i])); M[i], M[piv] = M[piv], M[i]
            for r in range(p):
                if r != i and M[i][i] != 0:
                    f = M[r][i] / M[i][i]
                    for c in range(i, p + 1): M[r][c] -= f * M[i][c]
        delta = [M[i][p] / M[i][i] for i in range(p)]
        beta = [b + d for b, d in zip(beta, delta)]
    ll = 0.0
    for xi, yi in zip(X, y):
        z = sum(b * v for b, v in zip(beta, xi)); pr = 1 / (1 + math.exp(-max(-30, min(30, z))))
        ll += yi * math.log(max(pr, 1e-12)) + (1 - yi) * math.log(max(1 - pr, 1e-12))
    return beta, ll
def labels(E, runs):
    out = []
    for x in runs:
        if x["solved"] and x["ev"] <= E: out.append((x, 1))
        elif x["ev"] >= E: out.append((x, 0))
    return out
for E in (300, 1000):
    print(f"\n== E={E}")
    lab = labels(E, k3r)
    X = [[1.0, math.log(x["mu"])] for x, _ in lab]; y = [yy for _, yy in lab]
    (b0, b1), ll = solve_lr(X, y)
    print(f"  logit P = {b0:.2f} + {b1:.2f} ln(mu)   n={len(lab)} pos={sum(y)} loglik={ll:.2f}")
    for p in (0.5, 0.8):
        print(f"  mu* at P={p}: {math.exp((math.log(p / (1 - p)) * -1 - b0) / b1):.2f}")
    lab2 = [(x, yy) for x, yy in lab if x["start"] is not None]
    X = [[1.0, math.log(x["mu"]), math.log(x["start"] + 1)] for x, _ in lab2]; y = [yy for _, yy in lab2]
    beta2, ll2 = solve_lr(X, y)
    print(f"  + ln(start+1): {beta2[0]:.2f} + {beta2[1]:.2f} ln(mu) + {beta2[2]:.2f} ln(start+1)  n={len(lab2)} loglik={ll2:.2f}")
    X = [[1.0, math.log(x["mu"]), float(x["D"] >= 11)] for x, _ in lab]
    beta3, ll3 = solve_lr(X, y=[yy for _, yy in lab])
    print(f"  + [D>=11]: {beta3[0]:.2f} + {beta3[1]:.2f} ln(mu) + {beta3[2]:.2f} [D>=11]  loglik={ll3:.2f}")
    X = [[1.0, math.log(x["mu"]), float(x["f"] == 0)] for x, _ in lab]
    beta4, ll4 = solve_lr(X, y=[yy for _, yy in lab])
    print(f"  + [f=0]: {beta4[0]:.2f} + {beta4[1]:.2f} ln(mu) + {beta4[2]:.2f} [f=0]  loglik={ll4:.2f}")
print("\nstart cost by mu bin, k=3 (all runs with start):")
for lo, hi in [(0, 4), (4, 8), (8, 12), (12, 16), (16, 25), (25, 1e9)]:
    s = sorted(x["start"] for x in k3r if x["start"] is not None and lo <= x["mu"] < hi)
    if s: print(f"  mu in [{lo},{hi}): n={len(s)} median start={s[len(s)//2]} p80={s[int(0.8*(len(s)-1))]}")
print("\nP(solve<=1000) by start-cost bin, mu>=8 (conditional labels):")
for lo, hi in [(0, 10), (10, 30), (30, 100), (100, 1e9)]:
    sub = [x for x in k3r if x["mu"] >= 8 and x["start"] is not None and lo <= x["start"] < hi]
    lab = [(x, 1 if (x["solved"] and x["ev"] <= 1000) else 0) for x in sub if x["solved"] or x["ev"] >= 1000]
    if lab: print(f"  start in [{lo},{hi}): n={len(lab)} P={sum(y for _, y in lab)/len(lab):.2f}")
