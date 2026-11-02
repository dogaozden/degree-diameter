"""c1 driver: run orbdfs on G-sets (est < THRESH) sequentially, one process at a time, each under timeout 100 s.
usage: drive.py THRESH_EST EST_FILE... ; appends to squad/r1/c1/runs.tsv; skips files already logged there (resumable).
On TIMEOUT the G-set is split into SHARDS pieces (SHARD=i/m SHARDDEPTH=6), each run under timeout 100 s."""
import sys, os, subprocess, re, time
W = "/home/user/degree-diameter/research/squads/deep-37"
os.chdir(W)
thresh = float(sys.argv[1]); estfiles = sys.argv[2:]
SHARDS = int(os.environ.get("SHARDS", "16"))
BUDGET = float(os.environ.get("BUDGET", "300"))  # seconds of sharded search per G-set
R = "squad/r1/c1/runs.tsv"
done = set()
if os.path.exists(R):
    for ln in open(R):
        p = ln.split("\t")
        if p and p[0] and p[0] != "file": done.add(p[0])
jobs = []
for ef in estfiles:
    for ln in open(ef):
        p = ln.rstrip("\n").split(None, 2)
        if len(p) < 2: continue
        est = float(p[1]) if p[1] != "PROBE_TIMEOUT" else 1e30
        jobs.append((est, p[0], p[2] if len(p) > 2 else ""))
jobs.sort()
def log(line):
    with open(R, "a") as fh: fh.write(line + "\n")
def run(env_extra, tag, timeout=100):
    env = dict(os.environ, MAXSOL="200", **env_extra)
    t0 = time.time()
    try:
        out = subprocess.run(["nice", "-n", "15", "timeout", str(timeout), "bin/orbdfs", FILE, "7"], capture_output=True,
                             text=True, env=env).stdout
    except Exception as e:
        out = ""
    m = re.search(r"DONE nodes=(\d+) sols=(\d+) time=\S+( \(stopped at MAXSOL\))?", out)
    wall = time.time() - t0
    if m and "EXCLUDED_TWIN" in out:
        return "EXCL_TWIN", m.group(1), m.group(2), wall
    if m:
        st = "MAXSOL" if m.group(3) else "DONE"
        return st, m.group(1), m.group(2), wall
    nsol = out.count("SOL ")
    return "TIMEOUT", "-", str(nsol), wall
for est, f, desc in jobs:
    if f in done or est >= thresh: continue
    FILE = f
    tag = os.path.basename(f)[:-4]
    grp = f.split("/")[-3] + "_" + f.split("/")[-2]
    st, nodes, sols, wall = run({"SOLPREFIX": f"squad/r1/c1/sol/{grp}_{tag}"}, tag)
    log("\t".join([f, grp, f"{est:.3e}", st, nodes, sols, f"{wall:.0f}", "-", desc.strip()]))
    if st == "TIMEOUT":
        spent = 0.0; complete = True
        for i in range(SHARDS):
            if spent > BUDGET:
                complete = False; break
            st2, nodes2, sols2, wall2 = run({"SHARD": f"{i}/{SHARDS}", "SHARDDEPTH": "6",
                                             "SOLPREFIX": f"squad/r1/c1/sol/{grp}_{tag}_s{i}"}, tag)
            spent += wall2
            log("\t".join([f, grp, f"{est:.3e}", st2, nodes2, sols2, f"{wall2:.0f}", f"{i}/{SHARDS}", desc.strip()]))
        if not complete:
            log("\t".join([f, grp, f"{est:.3e}", "UNRESOLVED", "-", "-", f"{spent:.0f}", "budget", desc.strip()]))
print("ALLDONE", flush=True)
