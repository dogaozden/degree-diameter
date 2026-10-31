#!/usr/bin/env python3
"""Run a queue of haar_sd jobs, P at a time.  QUEUE lines: TAG|ENV assignments (shell syntax)|d D secs seed K|GROUP... n
Each job: THREADS=1 ENV haar_sd d D secs seed K OUTDIR/TAG.sol GROUP... n > OUTDIR/TAG.log; jobs whose log exists are skipped.
usage: hsd_queue.py QUEUE OUTDIR P"""
import os, shlex, subprocess, sys
from concurrent.futures import ThreadPoolExecutor
here = os.path.dirname(os.path.abspath(__file__))
q, out, P = sys.argv[1], sys.argv[2], int(sys.argv[3])
os.makedirs(out, exist_ok=True)
jobs = [l.rstrip('\n').split('|') for l in open(q) if l.strip() and not l.startswith('#')]
def run(j):
    tag, envs, pre, grp = j
    log = os.path.join(out, tag + '.log')
    if os.path.exists(log) or os.path.exists(os.path.join(out, 'STOP')): return
    env = dict(os.environ, THREADS='1')
    for a in shlex.split(envs):
        k, v = a.split('=', 1); env[k] = v
    cmd = ['nice', '-n', '5', os.path.join(here, 'haar_sd')] + pre.split() + [os.path.join(out, tag + '.sol')] + grp.split()
    with open(log, 'w') as f: subprocess.run(cmd, stdout=f, stderr=subprocess.STDOUT, env=env)
with ThreadPoolExecutor(P) as ex: list(ex.map(run, jobs))
