"""c1 calibration: parse RESULT lines in logs/*.out; fit log(evals) = a + b*mu over the SOLVED runs (card rule).
Cross-check: censored exponential MLE, unsolved runs entered as lower bounds (their eval count at the budget end).
Groups mu 25.0 and 29.9 were not run (lanes stopped, machine load); they are listed as NOT RUN and excluded."""
import re, math, os
HERE = os.path.dirname(os.path.abspath(__file__))
W = 183063616  # d*sum_{i<4}(d-1)^(2i), d=16, D=8
GROUPS = [("43", "163"), ("41", "193"), ("53", "91"), ("37", "271"), ("61", "61"), ("37", "277")]
rx = re.compile(r'RESULT d=16 D=8 group=sl (\d+) x Z_(\d+) N=(\d+) best=(-?\d+) evals=(\d+) time=([\d.]+)')
runs = []
for p, n in GROUPS:
    for seed in (1, 2):
        f = os.path.join(HERE, "logs", "sl%sx%s_s%d.out" % (p, n, seed))
        m = rx.search(open(f).read()) if os.path.exists(f) else None
        if not m:
            runs.append(dict(tag="sl %s x %s" % (p, n), seed=seed, notrun=True)); continue
        N = int(m.group(3))
        runs.append(dict(tag="sl %s x %s" % (p, n), seed=seed, N=N, mu=N * math.exp(-W / N), best=int(m.group(4)),
                         evals=int(m.group(5)), time=float(m.group(6)), solved=int(m.group(4)) == 0))
ran = [r for r in runs if not r.get("notrun")]
S = [r for r in ran if r["solved"]]
out = ["group          N          mu     seed  solved  best  evals   time_s  evals/s  ln(evals)"]
for r in runs:
    if r.get("notrun"):
        out.append("%-14s NOT RUN (lanes stopped: machine load)" % r["tag"]); continue
    out.append("%-14s %-10d %6.2f  %d     %-6s  %-5d %-7d %-7.1f %-8.1f %s" % (
        r["tag"], r["N"], r["mu"], r["seed"], r["solved"], r["best"], r["evals"], r["time"], r["evals"] / r["time"],
        ("%.3f" % math.log(r["evals"])) if r["solved"] else "- (unsolved: censored)"))
out.append("solved %d of %d runs that were run" % (len(S), len(ran)))
if len(S) >= 2:
    xs = [r["mu"] for r in S]; ys = [math.log(r["evals"]) for r in S]
    mx, my = sum(xs) / len(xs), sum(ys) / len(ys)
    sxx = sum((x - mx) ** 2 for x in xs); sxy = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
    b = sxy / sxx; a = my - b * mx
    ssr = sum((y - (a + b * x)) ** 2 for x, y in zip(xs, ys)); sst = sum((y - my) ** 2 for y in ys)
    dof = len(xs) - 2
    se_b = math.sqrt(ssr / dof / sxx) if dof > 0 else float("nan")
    out.append("OLS on solved runs (natural log): a = %.4f  b = %.4f +- %.3f (1 sigma, dof %d)  R^2 = %.3f" % (
        a, b, se_b, dof, 1 - ssr / sst if sst > 0 else float("nan")))
    out.append("theory 1/4.5 would give b = 0.222")
    top = max(S, key=lambda r: r["mu"])
    out.append("largest mu solved = %.2f (%s, seed %d)" % (top["mu"], top["tag"], top["seed"]))
    out.append("largest mu run = %.2f: %d of 2 seeds solved (best costs %s)" % (
        max(r["mu"] for r in ran), sum(1 for r in ran if r["mu"] > 21 and r["solved"]), ", ".join(str(r["best"]) for r in ran if r["mu"] > 21)))
    obs = [(r["mu"], r["evals"], r["solved"]) for r in ran]
    ns = sum(1 for _, _, s in obs if s); sum_mu_s = sum(mu for mu, _, s in obs if s)
    def Lb(bb):
        A = sum(x * math.exp(-bb * mu) for mu, x, _ in obs)
        return -ns * math.log(A / ns) - bb * sum_mu_s - ns
    bb = max([i / 1000 for i in range(0, 601)], key=Lb)
    aa = math.log(sum(x * math.exp(-bb * mu) for mu, x, _ in obs) / ns)
    out.append("censored exponential MLE (cross-check, unsolved as lower bounds): a = %.3f  b = %.3f" % (aa, bb))
txt = "\n".join(out) + "\n"
print(txt, end="")
open(os.path.join(HERE, "results.txt"), "w").write(txt)
