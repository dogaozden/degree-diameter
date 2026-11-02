"""queue.py PAR TLIMIT est.txt... : run orbdfs on G-sets in increasing Knuth-estimate order, PAR jobs at a time,
TLIMIT seconds each; append results to runs/sweep/results.tsv (file, est, status, nodes, sols, time, desc).
Skips files already in results.tsv."""
import sys, subprocess, os, time, re
from concurrent.futures import ThreadPoolExecutor
par, tl = int(sys.argv[1]), int(sys.argv[2])
done = set()
R = os.environ.get("RESULTS", "runs/sweep/results.tsv")
if os.path.exists(R):
    for ln in open(R): done.add(ln.split("\t")[0])
jobs = []
for fn in sys.argv[3:]:
    for ln in open(fn):
        p = ln.split(None, 2)
        if len(p) < 2 or p[0] in done: continue
        est = float(p[1]) if p[1] != "PROBE_TIMEOUT" else 1e30
        jobs.append((est, p[0], p[2].strip() if len(p) > 2 else ""))
jobs.sort()
def run(j):
    est, f, desc = j
    pre = f[:-4] + "_sol"
    env = dict(os.environ, MAXSOL="50", SOLPREFIX=pre)
    t0 = time.time()
    try:
        out = subprocess.run([os.environ.get("BIN", "bin/orbdfs"), f, "7"], capture_output=True, text=True, timeout=tl, env=env).stdout
        m = re.search(r"DONE nodes=(\d+) sols=(\d+)", out)
        st, nodes, sols = ("DONE", m.group(1), m.group(2)) if m else ("ERR", "-", "-")
    except subprocess.TimeoutExpired as e:
        out = (e.stdout or b"").decode() if isinstance(e.stdout, bytes) else (e.stdout or "")
        st, nodes, sols = "TIMEOUT", "-", str(out.count("SOL "))
    line = "\t".join([f, f"{est:.2e}", st, nodes, sols, f"{time.time()-t0:.0f}", desc]) + "\n"
    with open(R, "a") as fh: fh.write(line)
    if sols not in ("0", "-"): 
        with open("runs/sweep/FOUND.txt", "a") as fh: fh.write(line)
with ThreadPoolExecutor(par) as ex: list(ex.map(run, jobs))
