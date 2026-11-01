# Calibration of the size law mu = N exp(-W/N) against solve effort (evals), from parsed lab logs.
import csv, math, random, sys
CSV = "/home/user/degree-diameter/research/squads/beyond11/r1/c15/runs.csv"
def W(d, D):
    if D % 2 == 0: return sum(d * (d - 1) ** (2 * i) for i in range(D // 2))
    return 1 + sum(d * (d - 1) ** (2 * i - 1) for i in range(1, (D - 1) // 2 + 1))
def Phi(x): return 0.5 * (1 + math.erf(x / math.sqrt(2)))
def Phiinv(p):
    lo, hi = -10.0, 10.0
    for _ in range(200):
        m = (lo + hi) / 2
        if Phi(m) < p: lo = m
        else: hi = m
    return (lo + hi) / 2

rows = []; seen = set()
for r in csv.DictReader(open(CSV)):
    if not r["N"] or not r["evals"] or not r["d"]: continue
    d, D, N = int(r["d"]), int(r["D"]), int(r["N"])
    key = (d, D, r["group"], N, r["orbit"], r["start"], r["best"], r["evals"], r["time"], r["status"])
    if key in seen: continue
    seen.add(key)
    k, m, f = (int(x) for x in r["orbit"].split()) if r["orbit"] else (0, 0, 0)
    mu = N * math.exp(-W(d, D) / N)
    ev = int(r["evals"]); solved = int(r["solved"]); st = int(r["start"]) if r["start"] else None
    rows.append(dict(d=d, D=D, N=N, grp=r["group"], k=k, m=m, f=f, mu=mu, ev=ev, solved=solved,
                     start=st, best=int(r["best"]), src=r["src"], file=r["file"], status=r["status"]))
print("unique runs:", len(rows), " solved:", sum(x["solved"] for x in rows))
k3 = [x for x in rows if x["k"] == 3]
print("k=3 runs:", len(k3), " solved:", sum(x["solved"] for x in k3))
# Kaplan-Meier for time to solve, binned by mu
def km_prob(data, E):
    # data: list of (time, event); returns P(T <= E) by Kaplan-Meier (censored runs contribute to risk set)
    data = sorted(data)
    S = 1.0; n = len(data); i = 0
    while i < n:
        t = data[i][0]; if_ev = 0; cnt = 0
        j = i
        while j < n and data[j][0] == t:
            cnt += 1
            if data[j][1]: if_ev += 1
            j += 1
        if t > E: break
        at_risk = n - i
        if if_ev: S *= (1 - if_ev / at_risk)
        i = j
    return 1 - S
bins = [(0, 1.5), (1.5, 2.5), (2.5, 3.5), (3.5, 4.5), (4.5, 6), (6, 9), (9, 15), (15, 1e9)]
print("\nKM P(solved within E evals) by mu bin, k=3 runs")
print("mu bin        n  solved  med_evals(solved)   P<=300  P<=1000  P<=3000")
for lo, hi in bins:
    sub = [x for x in k3 if lo <= x["mu"] < hi]
    if not sub: continue
    dat = [(x["ev"], x["solved"]) for x in sub]
    sv = sorted(x["ev"] for x in sub if x["solved"])
    med = sv[len(sv)//2] if sv else None
    print(f"[{lo:>4},{hi:>5})  {len(sub):>3}  {sum(x['solved'] for x in sub):>5}  {str(med):>12}  "
          f"{km_prob(dat,300):8.2f} {km_prob(dat,1000):8.2f} {km_prob(dat,3000):8.2f}")

# Parametric AFT model: log T ~ Normal(a + b*ln(mu) [+ c*ln(start)], s); censoring at ev for unsolved.
def nll(th, data):
    a, b, ls = th; s = math.exp(ls); tot = 0.0
    for x, t, ev in data:
        z = (math.log(t) - a - b * x) / s
        if ev:
            tot -= -0.5 * z * z - math.log(s) - 0.5 * math.log(2 * math.pi) if False else (-0.5 * z * z - math.log(s * t) - 0.5 * math.log(2 * math.pi))
        else:
            sf = 1 - Phi(z)
            tot -= math.log(max(sf, 1e-300))
    return tot
def fit(data):
    th = [0.0, 0.5, 0.0]; best = nll(th, data); step = [1.0, 0.5, 0.5]
    for it in range(6000):
        improved = False
        for i in range(3):
            for sgn in (1, -1):
                cand = list(th); cand[i] += sgn * step[i]
                v = nll(cand, data)
                if v < best: best, th, improved = v, cand, True
        if not improved:
            step = [x * 0.5 for x in step]
            if max(step) < 1e-5: break
    return th, best
data = [(math.log(x["mu"]), x["ev"], x["solved"]) for x in k3]
data = [(x, t, ev) for x, t, ev in data]
# Here the regressor is ln(mu); the observed time is evals (censored at ev for unsolved runs).
dat1 = [(math.log(x["mu"]), max(x["ev"], 1), x["solved"]) for x in k3]
th, val = fit(dat1)
a, b, ls = th; s = math.exp(ls)
print(f"\nAFT lognormal fit (k=3, n={len(k3)}): ln(evals) = {a:.3f} + {b:.3f} ln(mu) + eps, sigma={s:.3f}, nll={val:.2f}")
for E in (300, 1000):
    for p in (0.5, 0.8):
        # P(T<=E | mu) = Phi((ln E - a - b ln mu)/s) = p  ->  ln mu = (ln E - a - s*Phi^-1(p)) / b
        lm = (math.log(E) - a - s * Phiinv(p)) / b
        print(f"  E={E:>5} P(solve)>={p}: mu* = {math.exp(lm):.2f}")
# Add start cost covariate (solved and censored runs with a known start cost)
dat2 = [(math.log(x["mu"]), math.log(x["start"]), max(x["ev"], 1), x["solved"]) for x in k3 if x["start"]]
def nll2(th, data):
    a, b, c, ls = th; s = math.exp(ls); tot = 0.0
    for xm, xs, t, ev in data:
        z = (math.log(t) - a - b * xm - c * xs) / s
        if ev: tot -= (-0.5 * z * z - math.log(s * t) - 0.5 * math.log(2 * math.pi))
        else: tot -= math.log(max(1 - Phi(z), 1e-300))
    return tot
th2 = [a, b, 0.0, ls]; best2 = nll2(th2, dat2); step = [0.5, 0.2, 0.2, 0.2]
for it in range(8000):
    imp = False
    for i in range(4):
        for sg in (1, -1):
            c2 = list(th2); c2[i] += sg * step[i]; v = nll2(c2, dat2)
            if v < best2: best2, th2, imp = v, c2, True
    if not imp:
        step = [x * 0.5 for x in step]
        if max(step) < 1e-5: break
print(f"AFT with ln(start cost) covariate (n={len(dat2)}): a={th2[0]:.3f} b(ln mu)={th2[1]:.3f} c(ln start)={th2[2]:.3f} sigma={math.exp(th2[3]):.3f}")
# Residual check by cell: mean of (ln evals - fit) for solved runs, grouped by D and by d
print("\nResidual (solved runs, ln evals - AFT prediction) by D and by d:")
from collections import defaultdict
byD = defaultdict(list); byd = defaultdict(list)
for x in k3:
    if x["solved"]:
        res = math.log(x["ev"]) - (a + b * math.log(x["mu"]))
        byD[x["D"]].append(res); byd[x["d"]].append(res)
for name, grp in (("D", byD), ("d", byd)):
    for key in sorted(grp):
        v = grp[key]; print(f"  {name}={key}: n={len(v)} mean resid={sum(v)/len(v):+.2f}")
