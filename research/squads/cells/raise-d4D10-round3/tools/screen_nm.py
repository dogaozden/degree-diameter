"""RANDSAMPLE-200 screen (same call as round-2 screen_all.py) with haar_nm. Usage: screen_nm.py CANDS OUT [WORKERS]"""
import os, subprocess, sys
from concurrent.futures import ThreadPoolExecutor
BIN = os.environ.get("HAAR", "/tmp/claude-0/-home-user-degree-diameter/d68c5ced-3930-535c-a641-3fa3cd4e68f4/scratchpad/bin/haar_nm")
cands = []
for line in open(sys.argv[1]):
    if "|" not in line: continue
    N, spec = line.rstrip("\n").split("|")
    cands.append((int(N), spec))
def run(c):
    N, spec = c
    env = dict(os.environ, RANDSAMPLE="200", THREADS="1")
    try:
        r = subprocess.run([BIN, "4", "10", "1", "1", "8", "/dev/null"] + spec.split(), env=env,
                           capture_output=True, text=True, timeout=300).stdout
        kv = dict(x.split("=", 1) for x in r.split() if "=" in x and x.split("=", 1)[1].lstrip("-").isdigit())
        return (N, spec, int(kv["min"]), int(kv["p10"]), int(kv["median"]))
    except Exception as e:
        return (N, spec, None, None, str(e)[:60])
workers = int(sys.argv[3]) if len(sys.argv) > 3 else 4
with open(sys.argv[2], "w") as f, ThreadPoolExecutor(workers) as ex:
    for N, spec, mn, p10, med in ex.map(run, cands):
        f.write(f"{N}\t{spec}\t{mn if mn is not None else 'ERR'}\t{p10 if p10 is not None else ''}\t{med}\n")
        f.flush()
open(sys.argv[2] + ".done", "w").write("done\n")
