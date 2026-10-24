import json, os, re, subprocess, sys
from concurrent.futures import ThreadPoolExecutor
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from mc import prim_root
REPO = "/home/user/degree-diameter"
BIN = os.environ["BIN"]
SECS = int(os.environ.get("SECS", "60"))
TAG = os.environ.get("TAG", "sweep1")
def meta(p, k, n):
    g = prim_root(p); r = pow(g, (p - 1) // k, p)
    return ["meta", str(p), str(k), str(r)], n, f"meta Z_{p} x| Z_{k} x Z_{n} (r of order {k} mod {p})"
def agl(q, n):
    return ["agl1", str(q)], n, f"AGL(1,{q}) x Z_{n}"
JOBS = [agl(127,1), agl(128,1), agl(73,3), agl(16,66), agl(25,27), agl(49,7), agl(32,16), agl(64,4),
        agl(37,12), agl(41,10),
        meta(3989,4,1), meta(1601,10,1), meta(757,21,1), meta(379,42,1), meta(337,48,1),
        meta(673,12,2), meta(541,30,1), meta(1163,14,1), meta(1753,3,3), meta(2017,4,2),
        meta(811,5,4), meta(257,32,2), meta(613,9,3), meta(2647,6,1)]
def run(i_job):
    i, (grp, n, desc) = i_job
    tag = f"{TAG}_{i:02d}_{'_'.join(grp).replace(' ','_')}_n{n}"
    out = f"{REPO}/research/squads/alone/3/sols/{tag}.txt"
    cmd = [BIN, "16", "5", str(SECS), str(100 + i), "4", out] + grp + [str(n)]
    env = dict(os.environ, THREADS="1")
    p = subprocess.run(cmd, capture_output=True, text=True, env=env)
    res = [l for l in p.stdout.splitlines() if l.startswith("RESULT")]
    line = res[0] if res else p.stdout[-300:] + p.stderr[-300:]
    with open(f"{REPO}/research/squads/alone/3/logs/{tag}.log", "w") as f: f.write(p.stdout + p.stderr)
    m = re.search(r"best=(\d+)", line); best = int(m.group(1)) if m else None
    N = int(re.search(r"N=(\d+)", line).group(1)) if re.search(r"N=(\d+)", line) else None
    return dict(idea=f"{desc}; {TAG}", command=" ".join(["haar_gen3 16 5", str(SECS), str(100+i), "4", "<out>"] + grp + [str(n)]),
                score=best, valid=(best == 0), N=N, vertices=2*N if N else None)
with ThreadPoolExecutor(4) as ex:
    rows = list(ex.map(run, enumerate(JOBS)))
with open(f"{REPO}/research/squads/alone/3/scoreboard.jsonl", "a") as f:
    for r in rows: f.write(json.dumps(r) + "\n")
for r in rows: print(r["N"], r["score"], r["idea"][:70])
