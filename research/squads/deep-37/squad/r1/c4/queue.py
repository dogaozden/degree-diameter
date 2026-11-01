"""queue.py EST_FILE... : orbdfs (D=7) on each G-set in increasing PROBE-estimate order, one at a time, TL s each.
Appends to squad/r1/c4/runs.tsv (file, est, status, nodes, sols, secs, desc). Skips files already in runs.tsv."""
import sys, subprocess, os, time, re
TL = int(os.environ.get("TL", "100"))
R = "squad/r1/c4/runs.tsv"
done = set()
if os.path.exists(R):
    for ln in open(R): done.add(ln.split("\t")[0])
jobs = []
for fn in sys.argv[1:]:
    for ln in open(fn):
        p = ln.split(None, 2)
        if len(p) < 2 or p[0] in done: continue
        est = float(p[1]) if p[1] != "PROBE_TIMEOUT" else 1e30
        if est > float(os.environ.get("LIM", "5e6")): continue
        jobs.append((est, p[0], p[2].strip() if len(p) > 2 else ""))
jobs.sort()
for est, f, desc in jobs:
    pre = f[:-4] + "_sol"
    env = dict(os.environ, MAXSOL="20", SOLPREFIX=pre)
    t0 = time.time()
    try:
        out = subprocess.run(["nice", "-n", "15", "bin/orbdfs", f, "7"], capture_output=True, text=True, timeout=TL, env=env).stdout
        m = re.search(r"DONE nodes=(\d+) sols=(\d+)", out)
        st, nodes, sols = ("DONE", m.group(1), m.group(2)) if m else ("ERR", "-", "-")
    except subprocess.TimeoutExpired as e:
        out = (e.stdout or b"").decode() if isinstance(e.stdout, bytes) else (e.stdout or "")
        st, nodes, sols = "TIMEOUT", "-", str(out.count("SOL "))
    line = "\t".join([f, f"{est:.2e}", st, nodes, sols, f"{time.time()-t0:.0f}", desc]) + "\n"
    with open(R, "a") as fh: fh.write(line)
    print(line.strip()[:200], flush=True)
