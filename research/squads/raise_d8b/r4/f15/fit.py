import csv, math, numpy as np
D = "/home/user/degree-diameter/research/squads/raise_d8b/r4/f15/"
rows = [r for r in csv.DictReader(open(D + "runs.tsv"), delimiter="\t") if r["status"] in ("solved", "unsolved")]
ev = np.array([float(r["evals"]) for r in rows]); y = np.log(ev)
ev_flag = np.array([int(r["solved"]) for r in rows])  # 1 = event (solved), 0 = censored
mk = np.array([float(r["mu_k"]) for r in rows]); f = np.array([float(r["f"]) for r in rows])
f0 = np.array([1.0 if int(r["f"]) == 0 else 0.0 for r in rows]); lnN = np.log(np.array([float(r["N"]) for r in rows]))
Phi = lambda z: 0.5 * (1 + np.vectorize(math.erf)(z / math.sqrt(2)))
def nll(th, X):
    beta, ls = th[:-1], th[-1]; s = math.exp(ls)
    mu = X @ beta; z = (y - mu) / s
    ll_ev = -0.5 * z**2 - 0.5 * math.log(2 * math.pi) - ls - y  # density of log-evals (Jacobian -y cancels: fit on log scale)
    ll_ev = -0.5 * z**2 - 0.5 * math.log(2 * math.pi) - ls
    surv = 1 - Phi(z); surv = np.clip(surv, 1e-300, None)
    ll = np.where(ev_flag == 1, ll_ev, np.log(surv))
    return -ll.sum()
def nelder(fun, x0, step=0.5, iters=4000):
    n = len(x0); S = [np.array(x0, float)]
    for i in range(n):
        v = np.array(x0, float); v[i] += step; S.append(v)
    F = [fun(s) for s in S]
    for _ in range(iters):
        o = np.argsort(F); S = [S[i] for i in o]; F = [F[i] for i in o]
        if abs(F[-1] - F[0]) < 1e-10: break
        c = np.mean(S[:-1], axis=0); xr = c + (c - S[-1]); fr = fun(xr)
        if fr < F[0]:
            xe = c + 2 * (c - S[-1]); fe = fun(xe)
            S[-1], F[-1] = (xe, fe) if fe < fr else (xr, fr)
        elif fr < F[-2]:
            S[-1], F[-1] = xr, fr
        else:
            xc = c + 0.5 * (S[-1] - c); fc = fun(xc)
            if fc < F[-1]: S[-1], F[-1] = xc, fc
            else:
                S = [S[0] + 0.5 * (s - S[0]) for s in S]; F = [F[0]] + [fun(s) for s in S[1:]]
    i = int(np.argmin(F)); return S[i], F[i]
one = np.ones(len(y))
def fit(X, names):
    th0 = np.zeros(X.shape[1] + 1); th0[-1] = math.log(1.0)
    th, v = nelder(lambda t: nll(t, X), th0)
    th, v = nelder(lambda t: nll(t, X), th)
    return dict(zip(names + ["log_sigma"], th)), v
out = []
def P(*a):
    s = " ".join(str(x) for x in a); print(s); out.append(s)
P("runs in fit (completed, solved or censored at evals):", len(y), " solved:", int(ev_flag.sum()), " censored (unsolved):", int((1 - ev_flag).sum()))
P("")
# Model A: censored log-normal AFT, log(evals) = a + b*mu/k
XA = np.column_stack([one, mk]); pA, vA = fit(XA, ["a", "b_mu_over_k"])
P("MODEL A (censored log-normal AFT): log(evals) = a + b*mu/k")
P("  a=%.3f  b=%.3f  sigma=%.3f  nll=%.2f" % (pA["a"], pA["b_mu_over_k"], math.exp(pA["log_sigma"]), vA))
# Model B: + f
XB = np.column_stack([one, mk, f]); pB, vB = fit(XB, ["a", "b_mu_over_k", "c_f"])
P("MODEL B: log(evals) = a + b*mu/k + c*f")
P("  a=%.3f  b=%.3f  c=%.3f  sigma=%.3f  nll=%.2f" % (pB["a"], pB["b_mu_over_k"], pB["c_f"], math.exp(pB["log_sigma"]), vB))
# Model C: + ln N (group size), for information
XC = np.column_stack([one, mk, lnN]); pC, vC = fit(XC, ["a", "b_mu_over_k", "c_lnN"])
P("MODEL C: log(evals) = a + b*mu/k + c*ln(N)")
P("  a=%.3f  b=%.3f  c=%.3f  sigma=%.3f  nll=%.2f" % (pC["a"], pC["b_mu_over_k"], pC["c_lnN"], math.exp(pC["log_sigma"]), vC))
# Solved-only OLS (card's literal request), for comparison
s = ev_flag == 1
Xs = np.column_stack([one[s], mk[s]]); beta, *_ = np.linalg.lstsq(Xs, y[s], rcond=None)
res = y[s] - Xs @ beta; r2 = 1 - (res @ res) / ((y[s] - y[s].mean()) @ (y[s] - y[s].mean()))
P("")
P("SOLVED-ONLY OLS (n=%d): log(evals) = %.3f + %.3f*mu/k, residual sd %.3f, R2 %.3f" % (s.sum(), beta[0], beta[1], res.std(ddof=2), r2))
Xs3 = np.column_stack([one[s], mk[s], f[s]]); b3, *_ = np.linalg.lstsq(Xs3, y[s], rcond=None)
res3 = y[s] - Xs3 @ b3
P("SOLVED-ONLY OLS + f: log(evals) = %.3f + %.3f*mu/k + %.3f*f, residual sd %.3f" % (b3[0], b3[1], b3[2], res3.std(ddof=3)))
P("")
# Predicted evals median and P(solve within E evals) under model A and B
E = 7000  # ~1400 s at ~0.2 s/eval (median observed s/eval of completed runs)
sA = math.exp(pA["log_sigma"])
sp = np.array([float(r["s_per_eval"]) for r in rows if r["s_per_eval"] != ""])
P("median observed s/eval over completed runs: %.3f ; 1400 s / 0.2 s = %d evals" % (np.median(sp), 1400 / 0.2))
P("")
P("Model A predicted P(solved within %d evals) and median evals by mu/k:" % E)
for x in [4, 5, 6, 7, 8, 9, 10, 11, 12, 13]:
    med = math.exp(pA["a"] + pA["b_mu_over_k"] * x)
    pr = float(Phi(np.array([(math.log(E) - (pA["a"] + pA["b_mu_over_k"] * x)) / sA]))[0])
    P("  mu/k=%4.1f  median evals %8.0f  P(solve<=%d) %.2f" % (x, med, E, pr))
P("")
# Empirical table by mu/k bins
P("EMPIRICAL by mu/k bin (completed runs): n, solved, solved within %d evals, median evals of solved, unsolved censor range" % E)
bins = [(0, 6), (6, 7), (7, 8), (8, 9), (9, 10), (10, 11), (11, 15)]
for lo, hi in bins:
    idx = [i for i in range(len(y)) if lo <= mk[i] < hi]
    if not idx: P("  [%g,%g): none"); continue
    sol = [i for i in idx if ev_flag[i] == 1]; un = [i for i in idx if ev_flag[i] == 0]
    within = sum(1 for i in sol if ev[i] <= E)
    med = np.median([ev[i] for i in sol]) if sol else float("nan")
    cens = ("%d-%d" % (min(ev[i] for i in un), max(ev[i] for i in un))) if un else "-"
    P("  [%4.1f,%4.1f): n=%2d solved=%2d within%d=%2d median_solved=%s unsolved_evals=%s" % (lo, hi, len(idx), len(sol), E, within, ("%.0f" % med) if sol else "-", cens))
P("")
P("UNSOLVED with mu/k >= 9 (all completed unsolved runs, evals at end, best cost):")
for i, r in enumerate(rows):
    if ev_flag[i] == 0 and mk[i] >= 9:
        P("  mu/k=%6.3f (%s,8) %-16s k=%s m=%s f=%s evals=%6.0f best=%s" % (mk[i], r["d"], r["group"], r["k"], r["m"], r["f"], ev[i], r["best"]))
P("")
P("SOLVED with mu/k >= 9:")
for i, r in enumerate(rows):
    if ev_flag[i] == 1 and mk[i] >= 9:
        P("  mu/k=%6.3f (%s,8) %-16s k=%s m=%s f=%s evals=%6.0f" % (mk[i], r["d"], r["group"], r["k"], r["m"], r["f"], ev[i]))
open(D + "fit.txt", "w").write("\n".join(out) + "\n")
