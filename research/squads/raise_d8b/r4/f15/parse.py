import glob, re, os, hashlib, csv, time
BASE = "/home/user/degree-diameter/research/squads/raise_d8b"
files = sorted(glob.glob(BASE + "/r*/*/*.log")) + sorted(glob.glob("/home/user/degree-diameter/research/frontier/raise_d8/runs/*.log"))
rows, seen, skipped = [], {}, []
now = time.time()
for f in files:
    if "old_s4w_buggy" in f:
        skipped.append((f, "buggy-named")); continue
    txt = open(f, errors="replace").read().splitlines()
    if not any(l.startswith("t=") for l in txt):
        skipped.append((f, "no search steps")); continue
    grp = [l for l in txt if l.startswith("group ")]
    alpha = [l for l in txt if l.startswith("alpha:")]
    if not grp or not alpha:
        skipped.append((f, "no group/alpha header (other tool)")); continue
    if "prod" in grp[0] or " poly " in grp[0]:
        skipped.append((f, "haar_sym group")); continue
    if "ORBIT" not in alpha[0]:
        skipped.append((f, "no ORBIT")); continue
    g = re.match(r"group (psl|sl) (\d+) x Z_(\d+), N=(\d+) \(2N=(\d+)\)", grp[0])
    if not g:
        skipped.append((f, "group parse")); continue
    typ, p, n, N, V = g.group(1), int(g.group(2)), int(g.group(3)), int(g.group(4)), int(g.group(5))
    o = re.search(r"ORBIT k=(\d+) m=(\d+) f=(\d+).*mu=([\d.]+)", alpha[0])
    k, m, fx, mu = int(o.group(1)), int(o.group(2)), int(o.group(3)), float(o.group(4))
    sc = [l for l in txt if l.startswith("start cost=")]
    start_cost = int(re.search(r"start cost=(\d+)", sc[0]).group(1)) if sc else None
    tl = [l for l in txt if l.startswith("t=")]
    last = tl[-1]
    ev_last = int(re.search(r"evals=(\d+)", last).group(1))
    best_last = int(re.search(r"best=(\d+)", last).group(1))
    t_last = float(re.search(r"t=([\d.]+)", last).group(1))
    res = [l for l in txt if l.startswith("RESULT")]
    if res:
        r = res[-1]
        solved = bool(re.search(r"best=0 ", r))
        evals = int(re.search(r" evals=(\d+)", r).group(1))
        tt = float(re.search(r" time=([\d.]+)", r).group(1))
        best = int(re.search(r" best=(\d+)", r).group(1))
        status = "solved" if solved else "unsolved"
        dd = int(re.search(r"d=(\d+)", r).group(1))
    else:
        solved = False; evals = ev_last; tt = t_last; best = best_last
        status = "running" if (now - os.path.getmtime(f)) < 600 else "unsolved_nores"
        dd = fx + k * m
    d = fx + k * m
    rnd = re.search(r"/(r\d)/", f)
    rnd = rnd.group(1) if rnd else "frontier"
    card = os.path.basename(os.path.dirname(f)) if rnd != "frontier" else "director"
    # dedupe identical runs (same first lines and same final evals)
    key = hashlib.md5(("\n".join(txt[:3]) + str(ev_last) + str(best_last)).encode()).hexdigest()
    if key in seen:
        skipped.append((f, "duplicate of " + seen[key])); continue
    seen[key] = f
    rows.append(dict(file=f.replace(BASE + "/", "").replace("/home/user/degree-diameter/research/frontier/raise_d8/", "frontier/"),
                     rnd=rnd, card=card, d=d, D=8, group=f"{typ} {p} x Z{n}", typ=typ, p=p, n=n, N=N, vertices=V,
                     k=k, m=m, f=fx, mu=mu, mu_k=round(mu / k, 4), status=status, solved=int(solved),
                     evals=evals, time_s=tt, best=best, start_cost=start_cost if start_cost is not None else "",
                     s_per_eval=round(tt / evals, 4) if evals else ""))
with open(BASE + "/r4/f15/runs.tsv", "w", newline="") as fh:
    w = csv.DictWriter(fh, fieldnames=list(rows[0].keys()), delimiter="\t")
    w.writeheader(); w.writerows(rows)
print("runs", len(rows), "skipped", len(skipped))
from collections import Counter
print(Counter(r["status"] for r in rows)); print(Counter(r["rnd"] for r in rows))
for s in skipped: print("SKIP", s[1], s[0].replace(BASE, ""))
