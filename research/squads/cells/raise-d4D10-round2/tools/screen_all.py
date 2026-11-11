"""Screen candidate specs with haar_gen3 RANDSAMPLE (same call as haar_cell.py). Usage: screen_all.py CANDS_FILE OUT_TSV [WORKERS]"""
import os, subprocess, sys
from concurrent.futures import ThreadPoolExecutor
BIN = os.environ.get("HAAR", "/tmp/claude-0/-home-user-degree-diameter/b452ef01-b49f-5c7b-990a-52fce27a99ee/scratchpad/haar_gen3")
cands = []
for line in open(sys.argv[1]):
    if "|" not in line: continue
    s, N = line.rstrip("\n").split("|")
    cands.append((int(N), s))
cands = sorted(set(cands))
def run(c):
    N, spec = c
    env = dict(os.environ, RANDSAMPLE="200", THREADS="1")
    try:
        r = subprocess.run([BIN, "4", "10", "1", "1", "8", "/dev/null"] + spec.split(), env=env,
                           capture_output=True, text=True, timeout=300).stdout
        kv = dict(x.split("=", 1) for x in r.split() if "=" in x)
        return (N, spec, int(kv["min"]), int(kv["p10"]), int(kv["median"]))
    except Exception as e:
        return (N, spec, None, None, str(e)[:60])
workers = int(sys.argv[3]) if len(sys.argv) > 3 else 4
with open(sys.argv[2], "w") as f, ThreadPoolExecutor(workers) as ex:
    for res in ex.map(run, cands):
        N, spec, mn, p10, med = res
        if mn is None:
            f.write(f"{N}\t{spec}\tERR\t{med}\n")
        else:
            f.write(f"{N}\t{spec}\t{mn}\t{p10}\t{med}\n")
        f.flush()
