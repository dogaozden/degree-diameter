"""run169.py DIR TL BUDGET [MAXFILES]: run orbdfs169 (D=7, n=169, degree-2 set from TAG.deg2) on every TAG_<i>.txt in DIR,
in numeric order of i (files are written in increasing orbit count), each with timeout TL seconds, stopping when BUDGET
seconds have elapsed. Files already in squad/r2/d2/runs.tsv are skipped. Each line of runs.tsv:
file  status(DONE|TIMEOUT|EXCL|ERR)  nodes  sols  secs  far_of_solutions  desc
Solutions (if any) are written as SOLPREFIX_k.edges and checked with bin/score37 (far must be 0)."""
import sys, os, re, subprocess, time, glob
BASE = "/home/user/degree-diameter/research/squads/deep-37"
D2 = BASE + "/squad/r2/d2"
BIN = D2 + "/orbdfs169"
RUNS = D2 + "/runs.tsv"
dirn, TL, BUDGET = sys.argv[1], float(sys.argv[2]), float(sys.argv[3])
maxfiles = int(sys.argv[4]) if len(sys.argv) > 4 else 10**9
done = set()
if os.path.exists(RUNS):
    for ln in open(RUNS):
        done.add(ln.split("\t")[0])
files = sorted(glob.glob(os.path.join(dirn, "*.txt")), key=lambda f: int(re.search(r"_(\d+)\.txt$", f).group(1)))
t0 = time.time(); k = 0
for f in files:
    if f in done or k >= maxfiles:
        continue
    if time.time() - t0 > BUDGET:
        break
    k += 1
    deg2 = open(f[:-4] + ".deg2").read().strip()
    desc = ""
    env = dict(os.environ, DEG2=deg2, MAXSOL="20", SOLPREFIX=f[:-4] + "_sol")
    ts = time.time()
    try:
        out = subprocess.run([BIN, f, "7"], capture_output=True, text=True, timeout=TL, env=env).stdout
        m = re.search(r"DONE nodes=(\d+) sols=(\d+)(.*)", out)
        if m:
            nodes, sols, tail = m.group(1), m.group(2), m.group(3)
            st = "EXCL" if "EXCLUDED" in tail else "DONE"
        else:
            nodes, sols, st = "-", str(out.count("SOL ")), "ERR"
    except subprocess.TimeoutExpired as e:
        nodes, sols, st = "-", "-", "TIMEOUT"
    secs = time.time() - ts
    far = "-"
    if sols not in ("0", "-") and st in ("DONE", "EXCL") or (st == "TIMEOUT" and os.path.exists(f[:-4] + "_sol_1.edges")):
        fars = []
        i = 1
        while os.path.exists(f[:-4] + "_sol_%d.edges" % i):
            r = subprocess.run([BASE + "/bin/score37", f[:-4] + "_sol_%d.edges" % i], capture_output=True, text=True, timeout=60)
            fars.append(r.stdout.strip().split()[-1] if r.stdout.strip() else "?")
            i += 1
        far = ",".join(fars)
    with open(RUNS, "a") as fh:
        fh.write("\t".join([f, st, nodes, sols, "%.1f" % secs, far, open(f).readline().strip()]) + "\n")
    print(f, st, nodes, sols, "%.1f" % secs, far, flush=True)
print("chunk done files=%d elapsed=%.0f" % (k, time.time() - t0))
