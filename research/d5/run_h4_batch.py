#!/usr/bin/env python3
"""Runs the Round 4 jobs in h4_jobs.txt: at most MAX at once, each under nice -n 15, plus the climb rule.

Launch (from the repo root, under the autopilot time limit and stop switch):
  nohup scripts/guarded.sh 10 research/d5/run_h4_batch.py > research/d5/logs/h4_batch.log 2>&1 &
Climb: when a job leaves a cost-0 solution in sols/h4_<tag>.txt, the next larger order of the same family for the
same Δ is queued at the front (h4_plan.next_larger), 30 min, seed 1, K 20. Each tag is queued once.
A TERM (from guarded.sh) goes to the running jobs; they stop and nothing new starts.
"""
import os
import signal
import subprocess
import sys
import time
from collections import deque

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import h4_plan  # noqa: E402

MAX = int(os.environ.get("MAX", 8))
JOBS = os.environ.get("JOBS", os.path.join(HERE, "h4_jobs.txt"))
SOLS = os.path.join(HERE, "sols")


def tag_of(d, table, seed, k):
    return f"d{d}_{table}_s{seed}_K{k}"


def load(path):
    jobs = []
    with open(path) as f:
        for line in f:
            line = line.strip()
            if line and not line.startswith("#"):
                d, table, secs, seed, k = line.split()
                jobs.append((int(d), table, secs, seed, k))
    return jobs


def log(msg):
    print(f"{time.strftime('%F %T')} {msg}", flush=True)


def main():
    queue = deque(load(JOBS))
    seen = {tag_of(*j[:2], j[3], j[4]) for j in queue}
    running = []  # (process, tag, d, table)
    stop = False

    def on_term(signum, frame):
        nonlocal stop
        stop = True
        log(f"signal {signum}: sending TERM to {len(running)} running jobs, starting nothing new")
        for proc, _, _, _ in running:
            proc.send_signal(signal.SIGTERM)

    signal.signal(signal.SIGTERM, on_term)
    signal.signal(signal.SIGINT, on_term)
    log(f"start: {len(queue)} jobs, MAX={MAX}")

    while True:
        for item in list(running):
            proc, tag, d, table = item
            if proc.poll() is None:
                continue
            running.remove(item)
            log(f"done {tag} exit={proc.returncode}")
            sol = os.path.join(SOLS, f"h4_{tag}.txt")
            if os.path.exists(sol) and os.path.getsize(sol) > 0:
                nxt = h4_plan.next_larger(table, d)
                if nxt is None:
                    log(f"cost 0 on {tag}: no larger order in the family")
                    continue
                job = (d, nxt, h4_plan.PART_B_SECS, 1, h4_plan.PART_B_K)
                t = tag_of(*job[:2], job[3], job[4])
                if t not in seen:
                    seen.add(t)
                    queue.appendleft(job)
                    log(f"cost 0 on {tag}: climb queued {t}")
        if not stop:
            while queue and len(running) < MAX:
                d, table, secs, seed, k = queue.popleft()
                tag = tag_of(d, table, seed, k)
                cmd = ["nice", "-n", "15", os.path.join(HERE, "run_h4.sh"), str(d), table, str(seed), secs, k]
                running.append((subprocess.Popen(cmd), tag, d, table))
                log(f"start {tag} secs={secs} (running {len(running)}, queued {len(queue)})")
        if not running and (stop or not queue):
            break
        time.sleep(5)
    log("all jobs finished" if not stop else "stopped")
    return 0


if __name__ == "__main__":
    sys.exit(main())
