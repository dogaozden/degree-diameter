"""Successive-halving driver for haar_gen3: many groups get a short run, the most promising get longer runs.

  python3 wave3/halving.py JOBFILE [--procs 3] [--stages 30,150,600] [--keep 0.34] [--bin ./haar_gen3]
                                   [--threads 1] [--stop-solved]
Run from research/frontier.  JOBFILE has batch.sh lines (d D seconds seed K group... n); the seconds field is ignored
and replaced by the stage times.  Stage s runs every surviving job with seed (seed + 1000*s) for stages[s] seconds;
after a stage, solved jobs are done (their solution stays in sols/), and of the unsolved jobs the fraction --keep with
the lowest final cost (ties: larger N first) go on to the next stage.  Files: sols/<tag>.txt and runs/<tag>.log with
the batch.sh tag of the stage's seed, so every run is reproducible with batch.sh/haar_gen3.
--stop-solved: once a job with order N is solved, unsolved jobs with order <= N are dropped (nothing to gain).
A summary line per run goes to stdout:  stage tag N best time.
"""
import argparse
import os
import re
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed

ap = argparse.ArgumentParser()
ap.add_argument("jobfile")
ap.add_argument("--procs", type=int, default=3)
ap.add_argument("--stages", default="30,150,600")
ap.add_argument("--keep", type=float, default=0.34)
ap.add_argument("--bin", default="./haar_gen3")
ap.add_argument("--threads", type=int, default=1)
ap.add_argument("--stop-solved", action="store_true")
a = ap.parse_args()
stages = [float(x) for x in a.stages.split(",")]

jobs = []
for ln in open(a.jobfile):
    t = ln.split()
    if not t or t[0].startswith("#"):
        continue
    d, D, _secs, seed, K = t[:5]
    grp = t[5:]
    jobs.append({"d": d, "D": D, "seed": int(seed), "K": K, "grp": grp})


def order_of(job, log):
    m = re.search(r"N=(\d+)", log)
    return int(m.group(1)) if m else 0


def run(job, stage):
    seed = job["seed"] + 1000 * stage
    tag = "d%sD%s_%s_s%d" % (job["d"], job["D"], "_".join(job["grp"]), seed)
    sol, log = "sols/%s.txt" % tag, "runs/%s.log" % tag
    if os.path.exists(sol):
        return job, tag, 0, 0.0, open(log).read() if os.path.exists(log) else ""
    env = dict(os.environ, THREADS=str(a.threads))
    with open(log, "w") as f:
        subprocess.run([a.bin, job["d"], job["D"], str(stages[stage]), str(seed), job["K"], sol] + job["grp"],
                       stdout=f, stderr=subprocess.STDOUT, env=env)
    txt = open(log).read()
    m = re.search(r"RESULT .* best=(\d+) evals=\d+ time=([\d.]+)", txt)
    best, tm = (int(m.group(1)), float(m.group(2))) if m else (10 ** 9, 0.0)
    return job, tag, best, tm, txt


alive = jobs
solved_max = 0
for s, secs in enumerate(stages):
    if not alive:
        break
    print("# stage %d: %d jobs x %.0f s" % (s, len(alive), secs), flush=True)
    results = []
    with ThreadPoolExecutor(max_workers=a.procs) as ex:
        futs = [ex.submit(run, j, s) for j in alive]
        for fu in as_completed(futs):
            job, tag, best, tm, txt = fu.result()
            N = order_of(job, txt)
            job["N"] = N
            print("stage%d %s N=%d best=%d time=%.1f" % (s, tag, N, best, tm), flush=True)
            if best == 0:
                solved_max = max(solved_max, N)
            else:
                results.append((best, -N, job))
    results.sort(key=lambda r: (r[0], r[1]))
    nkeep = max(1, int(round(len(results) * a.keep))) if results else 0
    alive = [r[2] for r in results[:nkeep]]
    if a.stop_solved:
        alive = [j for j in alive if j.get("N", 0) > solved_max]
print("# done; largest solved N = %d" % solved_max, flush=True)
