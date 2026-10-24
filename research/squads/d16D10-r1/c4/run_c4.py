#!/usr/bin/env python3
"""Card c4 (squad d16D10-r1): search-parameter sweep on sl 53 x Z91, ORBIT="3 5 1", proxy (16,8), mu = 18.25.

One parameter changed at a time against the default (K=8, TARGP=70, TMAX/TMIN 1.5/0.15, COOL 20 s, RESTART 0).
Two runs at a time (THREADS=1, timeout, nice -n 10), seeds 1..3, seed-major job order so that every variant
gets the early seeds first. Writes results.jsonl (one line per run) and table.txt (E18 per variant).
E18 = median(adjusted evals) * exp((18 - mu)/4.5); adjusted evals = evals if solved, else 3 * evals.
"""
import json, math, os, re, statistics, subprocess, sys, threading, time
from concurrent.futures import ThreadPoolExecutor, as_completed

T = "/tmp/claude-0/-home-user-degree-diameter/4ce63409-b0f8-5c33-8f23-00173ad34031/scratchpad/tools/research/structured"
HERE = os.path.dirname(os.path.abspath(__file__))
SOL = os.path.join(HERE, "sol")
LOG = os.path.join(HERE, "logs")
RES = os.path.join(HERE, "results.jsonl")
os.makedirs(SOL, exist_ok=True)
os.makedirs(LOG, exist_ok=True)

SEEDS = [1, 2, 3]
SECS = 60          # wall-clock annealing budget per run (card allows <= 120 s; 60 s keeps the card inside 20 min)
HARD = 90          # kill switch per run (setup ~2 s, plus a final full check for solved runs)
WORKERS = 2        # at most 2 runs at a time
DEADLINE_S = 600   # no run is started later than this many seconds after the driver starts

# name, K, extra environment, seconds argument
VARIANTS = [
    ("default", 8, {}, SECS),
    ("K4", 4, {}, SECS),
    ("K16", 16, {}, SECS),
    ("TARGP40", 8, {"TARGP": "40"}, SECS),
    ("TARGP95", 8, {"TARGP": "95"}, SECS),
    ("TMAX0.8_TMIN0.08", 8, {"TMAX": "0.8", "TMIN": "0.08"}, SECS),
    ("TMAX3_TMIN0.3", 8, {"TMAX": "3", "TMIN": "0.3"}, SECS),
    # default REHEAT=150 s is longer than any run here, so RESTART=1 alone is inert; REHEAT=20 makes it act
    ("RESTART1_REHEAT20_RSTEPS100", 8, {"RESTART": "1", "REHEAT": "20", "REHEATSTEPS": "100"}, SECS),
    # deterministic: one step = 0.01 virtual s, COOL=2 -> half-life 200 steps (= 20 s wall at K=8); MAXSTEPS = 600 steps
    ("VCLOCK0.01_COOL2", 8, {"VCLOCK": "0.01", "COOL": "2", "MAXSTEPS": "600"}, 1000),
]
JOBS = [(name, K, extra, secs, seed) for seed in SEEDS for (name, K, extra, secs) in VARIANTS]

LOCK = threading.Lock()
T0 = time.time()


def run_job(job):
    name, K, extra, secs, seed = job
    if time.time() - T0 > DEADLINE_S:
        return {"variant": name, "seed": seed, "skipped": True}
    tag = f"{name}_s{seed}"
    sol = os.path.join(SOL, tag + ".txt")
    env = {"PATH": os.environ.get("PATH", "/usr/bin:/bin"), "HOME": os.environ.get("HOME", "/root"),
           "ORBIT": "3 5 1", "THREADS": "1", "OMP_NUM_THREADS": "1"}
    env.update(extra)
    cmd = ["timeout", str(HARD), "nice", "-n", "10", os.path.join(T, "haar_sym"),
           "16", "8", str(secs), str(seed), str(K), sol, "sl", "53", "91"]
    t_start = time.time()
    p = subprocess.run(cmd, env=env, capture_output=True, text=True)
    wall = time.time() - t_start
    with open(os.path.join(LOG, tag + ".out"), "w") as f:
        f.write(p.stdout)
    with open(os.path.join(LOG, tag + ".err"), "w") as f:
        f.write(p.stderr)
    rec = {"variant": name, "seed": seed, "K": K, "env": extra, "secs": secs,
           "cmd": " ".join(["ORBIT='3 5 1'", "THREADS=1"] + [f"{k}={v}" for k, v in extra.items()] + cmd),
           "wall": round(wall, 1), "rc": p.returncode}
    m = re.search(r"RESULT .*? best=(\d+) evals=(\d+) time=([\d.]+)", p.stdout)
    mm = re.search(r"mu = ([\d.]+)", p.stderr)
    mc = re.search(r"full diameter check: (\w+)", p.stdout)
    rec["mu"] = float(mm.group(1)) if mm else None
    rec["check"] = mc.group(1) if mc else None
    if m:
        best, evals, tm = int(m.group(1)), int(m.group(2)), float(m.group(3))
        rec.update(best=best, evals=evals, time=tm, solved=(best == 0))
        rec["adj_evals"] = evals if best == 0 else 3 * evals
    else:
        rec["error"] = p.stderr[-400:]
    with LOCK:
        with open(RES, "a") as f:
            f.write(json.dumps(rec) + "\n")
    return rec


def main():
    print(f"driver start {time.strftime('%H:%M:%S')}, {len(JOBS)} jobs, SECS={SECS}, WORKERS={WORKERS}", flush=True)
    recs = []
    with ThreadPoolExecutor(max_workers=WORKERS) as ex:
        futs = [ex.submit(run_job, j) for j in JOBS]
        for fu in as_completed(futs):
            r = fu.result()
            recs.append(r)
            print(time.strftime('%H:%M:%S'), {k: r.get(k) for k in
                  ("variant", "seed", "best", "evals", "time", "wall", "rc", "check", "skipped", "error")}, flush=True)
    mu = next((r["mu"] for r in recs if r.get("mu")), None)
    lines = [f"mu={mu}  E18 = median(adj evals) * exp((18-mu)/4.5), adj = evals if solved else 3*evals",
             "variant                         K  solved  adj_evals(by seed)            median    E18     vs_default"]
    e18 = {}
    for name, K, extra, secs in VARIANTS:
        rs = sorted([r for r in recs if r["variant"] == name and "adj_evals" in r], key=lambda r: r["seed"])
        if not rs:
            continue
        adj = [r["adj_evals"] for r in rs]
        med = statistics.median(adj)
        e18[name] = med * math.exp((18 - mu) / 4.5)
        ns = sum(1 for r in rs if r["solved"])
        lines.append(f"{name:30s} {K:2d}  {ns}/{len(rs)}    {str(adj):28s}  {med:9.0f} {e18[name]:8.0f}")
    base = e18.get("default")
    if base:
        lines = [l + (f"  {e18[l.split()[0]] / base:6.2f}" if l.split()[0] in e18 and not l.startswith(("mu", "variant")) else "")
                 for l in lines]
    best = min(e18, key=e18.get) if e18 else None
    lines.append(f"best variant: {best}  E18={e18.get(best, float('nan')):.0f}")
    text = "\n".join(lines)
    with open(os.path.join(HERE, "table.txt"), "w") as f:
        f.write(text + "\n")
    print(text, flush=True)
    print(f"driver end {time.strftime('%H:%M:%S')}", flush=True)


if __name__ == "__main__":
    main()
