"""Card c2 scorer: E18 per group shape from the logs in c2/logs/.

E18 = median over seeds of evals-to-solve (an unsolved run counts as 3 x its evals) * exp((18 - mu)/4.5).
mu = N exp(-W/N), W = 183,063,616 for (d, D) = (16, 8). Run: python3 -I c2/score_c2.py
"""
import glob, json, math, os, re, statistics

HERE = os.path.dirname(os.path.abspath(__file__))
W = 16 * sum(15 ** (2 * i) for i in range(4))  # d * sum_{i<D/2} (d-1)^(2i) for d=16, D=8
SHAPES = [  # name, p, n, description
    ("n1", 239, 1, "n = 1 (no cyclic factor)"),
    ("small", 101, 13, "n = 13 (small cyclic factor)"),
    ("medium", 53, 91, "n = 91 (medium cyclic factor)"),
    ("large", 41, 199, "n = 199 (large cyclic factor)"),
]
PAT = re.compile(r"^(?P<shape>\w+)_sl(?P<p>\d+)_n(?P<n>\d+)_s(?P<seed>\d+)\.log$")
RES = re.compile(r"^RESULT d=16 D=8 group=sl (\d+) x Z_(\d+) N=(\d+) best=(\d+) evals=(\d+) time=([\d.]+)")

runs = {}
for path in sorted(glob.glob(os.path.join(HERE, "logs", "*.log"))):
    m = PAT.match(os.path.basename(path))
    if not m:
        continue
    text = open(path).read()
    r = re.compile(RES.pattern, re.M).search(text)
    if not r:
        continue
    p, n, N, best, evals, secs = int(r.group(1)), int(r.group(2)), int(r.group(3)), int(r.group(4)), int(r.group(5)), float(r.group(6))
    key = m.group("shape")
    runs.setdefault(key, []).append(dict(seed=int(m.group("seed")), p=p, n=n, N=N, best=best, evals=evals,
                                         time=secs, solved=(best == 0)))

summary = {}
print("shape   group          N          mu    seed  solved  evals   time_s  ms/eval  evals_eff")
for name, p, n, desc in SHAPES:
    rs = sorted(runs.get(name, []), key=lambda x: x["seed"])
    if not rs:
        print(name, "no runs")
        continue
    N = rs[0]["N"]
    mu = N * math.exp(-W / N)
    effs = []
    for r in rs:
        eff = r["evals"] if r["solved"] else 3 * r["evals"]
        effs.append(eff)
        msev = 1000 * r["time"] / r["evals"] if r["evals"] else float("nan")
        print("%-7s sl%d x Z_%d %10d %6.2f  %4d  %6s  %6d  %7.1f  %7.2f  %8d" % (
            name, r["p"], r["n"], N, mu, r["seed"], "yes" if r["solved"] else "NO", r["evals"], r["time"], msev, eff))
    med = statistics.median(effs)
    e18 = med * math.exp((18 - mu) / 4.5)
    summary[name] = dict(group="sl %d x Z_%d" % (rs[0]["p"], rs[0]["n"]), N=N, mu=round(mu, 2), seeds=len(rs),
                         solved=sum(r["solved"] for r in rs), median_evals_eff=med, E18=round(e18, 1),
                         best_cost=[r["best"] for r in rs], evals=[r["evals"] for r in rs])
print()
for name, s in summary.items():
    print("%-7s %-16s mu=%.2f solved %d/%d  median evals_eff=%.0f  E18=%.0f" % (
        name, s["group"], s["mu"], s["solved"], s["seeds"], s["median_evals_eff"], s["E18"]))
if summary:
    best = min(summary, key=lambda k: summary[k]["E18"])
    print("best shape:", best, "E18=%.0f" % summary[best]["E18"])
    for k, s in summary.items():
        if k != best:
            print("  %-7s / best = %.2f" % (k, s["E18"] / summary[best]["E18"]))
    json.dump(summary, open(os.path.join(HERE, "summary.json"), "w"), indent=1)
