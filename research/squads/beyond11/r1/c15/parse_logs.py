# Parse lab Haar-search run logs (git blobs from origin branch + working-tree logs) into runs.csv.
import re, subprocess, csv, sys, os
REPO = "/home/user/degree-diameter"
ORIG = "origin/claude/new-cells-beyond-etos3t"
SRC = []
ls = subprocess.run(["git", "-C", REPO, "ls-tree", "-r", "--name-only", ORIG, "research/frontier/beyond/runs"],
                    capture_output=True, text=True).stdout.split()
for p in ls:
    if p.endswith(".log"):
        txt = subprocess.run(["git", "-C", REPO, "show", f"{ORIG}:{p}"], capture_output=True, text=True).stdout
        SRC.append(("beyond-branch", p, txt))
for d, tag in [("research/structured/runs", "structured"), ("research/frontier/beyond11/runs", "beyond11")]:
    for fn in sorted(os.listdir(os.path.join(REPO, d))):
        if fn.endswith(".log"):
            SRC.append((tag, os.path.join(d, fn), open(os.path.join(REPO, d, fn), errors="replace").read()))

RE_RES = re.compile(r"^RESULT d=(\d+) D=(\d+) group=(\S+ \d+ x Z_\d+|\S+ \d+ x Z_\d+)\s+N=(\d+).*?best=(\d+) evals=(\d+)(?: steps=\d+)? time=([\d.]+)(.*)$")
RE_ORB = re.compile(r"ORBIT k=(\d+) m=(\d+) f=(\d+)")
RE_MU = re.compile(r"mu=([\d.]+)")
RE_START = re.compile(r"start cost=(\d+)")
RE_PROG = re.compile(r"evals=(\d+)")
RE_GROUP = re.compile(r"^group (\S+ \d+ x Z_\d+|\S+ \d+ x Z_\d+|\S[^,]*?) ?, ?N=(\d+)")
RE_GROUP2 = re.compile(r"^group (.+?), N=(\d+)")
RE_FN = re.compile(r"d(\d+)D(\d+)")

rows = []
for tag, path, txt in SRC:
    lines = txt.splitlines()
    fn_d = RE_FN.search(os.path.basename(path))
    hdr_group = None; hdr_N = None; hdr_mu = None; hdr_orb = None; start = None; last_evals = None; last_best = None
    hdr_mu_from_alpha = None
    for ln in lines:
        m = RE_GROUP2.match(ln)
        if m and hdr_group is None:
            hdr_group, hdr_N = m.group(1), int(m.group(2))
        if ln.startswith("alpha:") or ln.startswith("ORBIT") or "ORBIT k=" in ln:
            mo = RE_ORB.search(ln)
            if mo: hdr_orb = tuple(int(x) for x in mo.groups())
            mm = RE_MU.search(ln)
            if mm: hdr_mu = float(mm.group(1))
        ms = RE_START.search(ln)
        if ms and start is None:
            start = int(ms.group(1))
        mp = re.search(r"\bevals=(\d+)", ln)
        if mp and not ln.startswith("RESULT"):
            last_evals = int(mp.group(1))
            mb = re.search(r"best=(\d+)", ln)
            if mb: last_best = int(mb.group(1))
        mr = RE_RES.match(ln)
        if mr:
            d, D, grp, N, best, evals, tm, rest = mr.groups()
            mo = RE_ORB.search(rest) or None
            orb = tuple(int(x) for x in mo.groups()) if mo else hdr_orb
            mm = RE_MU.search(rest)
            mu = float(mm.group(1)) if mm else hdr_mu
            rows.append(dict(src=tag, file=path, d=int(d), D=int(D), group=grp, N=int(N), mu=mu,
                             orbit=("%d %d %d" % orb) if orb else "", start=start, best=int(best),
                             evals=int(evals), time=float(tm), status="result"))
            start = None
            # reset per-run header state after a RESULT (multi-run logs)
            hdr_mu = None; hdr_orb = None
    if not any(r["file"] == path for r in rows) and hdr_group is not None:
        # unfinished (killed/censored) run: last progress line
        rows.append(dict(src=tag, file=path, d=int(fn_d.group(1)) if fn_d else None, D=int(fn_d.group(2)) if fn_d else None,
                         group=hdr_group, N=hdr_N, mu=hdr_mu, orbit=("%d %d %d" % hdr_orb) if hdr_orb else "",
                         start=start, best=last_best, evals=last_evals, time=None, status="censored"))

for r in rows:
    if r["best"] is not None:
        r["solved"] = 1 if (r["status"] == "result" and r["best"] == 0) else 0
    else:
        r["solved"] = 0
out = os.path.join(REPO, "research/squads/beyond11/r1/c15/runs.csv")
keys = ["src", "file", "d", "D", "group", "N", "mu", "orbit", "start", "best", "evals", "time", "status", "solved"]
with open(out, "w", newline="") as f:
    w = csv.DictWriter(f, fieldnames=keys); w.writeheader()
    for r in rows: w.writerow({k: r.get(k) for k in keys})
print(len(rows), "runs written to", out)
