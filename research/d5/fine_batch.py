#!/usr/bin/env python3
"""Runs the fine-ladder jobs in fine_jobs_s<S>.txt: at most MAX at once, each under nice -n 15.

Launch (from the repo root, under the autopilot time limit and stop switch):
  scripts/guarded.sh 5 research/d5/fine_batch.py research/d5/fine_jobs_s1.txt > research/d5/logs/fine_batch_s1.log 2>&1 &
A job whose log already has its final best= line is skipped, so a restarted batch picks up where it stopped.
A TERM (from guarded.sh) goes to the running jobs; they stop and nothing new starts.
"""
import os
import signal
import subprocess
import sys
import time
from collections import deque

HERE = os.path.dirname(os.path.abspath(__file__))
MAX = int(os.environ.get("MAX", 4))


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


def done_before(tag):
    p = os.path.join(HERE, "logs", f"fine_{tag}.log")
    return os.path.exists(p) and "best=" in open(p).read()


def log(msg):
    print(f"{time.strftime('%F %T')} {msg}", flush=True)


def main(argv):
    queue = deque(load(argv[0]))
    running = []  # (process, tag)
    stop = False

    def on_term(signum, frame):
        nonlocal stop
        stop = True
        log(f"signal {signum}: sending TERM to {len(running)} running jobs, starting nothing new")
        for proc, _ in running:
            proc.send_signal(signal.SIGTERM)

    signal.signal(signal.SIGTERM, on_term)
    signal.signal(signal.SIGINT, on_term)
    log(f"start: {len(queue)} jobs, MAX={MAX}")
    while True:
        for item in list(running):
            proc, tag = item
            if proc.poll() is None:
                continue
            running.remove(item)
            sol = os.path.join(HERE, "sols", f"fine_{tag}.txt")
            hit = " COST0" if os.path.exists(sol) and os.path.getsize(sol) > 0 else ""
            log(f"done {tag} exit={proc.returncode}{hit}")
        if not stop:
            while queue and len(running) < MAX:
                d, table, secs, seed, k = queue.popleft()
                tag = tag_of(d, table, seed, k)
                if done_before(tag):
                    continue
                cmd = ["nice", "-n", "15", os.path.join(HERE, "run_fine.sh"),
                       str(d), table, str(seed), str(secs), str(k)]
                running.append((subprocess.Popen(cmd), tag))
                log(f"start {tag} secs={secs} (running {len(running)}, queued {len(queue)})")
        if not running and (stop or not queue):
            break
        time.sleep(5)
    log("all jobs finished" if not stop else "stopped")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
