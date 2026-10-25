#!/usr/bin/env python3
"""Run `lake build MOD` jobs under a memory budget, from a queue file that may grow while it runs (run from lean/).

usage: poolq.py QUEUE LOG BUDGET_GB MAXJOBS
QUEUE lines: `MOD:GB` (estimated peak memory; `!MOD:GB` runs `lean` on the module directly instead of
`lake build`), `--` (barrier: everything above finishes before anything below
starts), `END` (stop once everything above is done), blank or `#` lines are ignored. Lines may be appended at any
time. Between two barriers jobs start in any order as the budget allows (a large job does not block smaller ones
after it). Each finished job logs wall time, measured peak RSS and status; a failure logs the tail of its output."""
import os, subprocess, sys, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from poolbuild import ENV, lean_rss_by_ppid, tree_rss  # noqa: E402


def lean_env():
    env = dict(ENV)
    env['LEAN_PATH'] = subprocess.run(['lake', 'env', 'printenv', 'LEAN_PATH'], capture_output=True, text=True,
                                      env=ENV).stdout.strip()
    return env


LENV = lean_env()


def parse(path):
    items = []
    for line in open(path):
        line = line.strip()
        if not line or line.startswith('#'):
            continue
        if line in ('--', 'END'):
            items.append(line)
        else:
            m, g = line.rsplit(':', 1)
            items.append((m, float(g)))
    return items


def main():
    qpath, log, budget, maxjobs = sys.argv[1], sys.argv[2], float(sys.argv[3]), int(sys.argv[4])
    os.makedirs('/tmp/claude-0/logs/jobs', exist_ok=True)
    running = {}  # pid -> (index, mod, est, t0, popen, peak)
    started, finished = set(), set()
    while True:
        procs = lean_rss_by_ppid()
        for pid, (k, m, est, t0, p, peak) in list(running.items()):
            own = procs.get(pid, ('', 0, 0))[2] if m.startswith('!') else 0
            peak = max(peak, own + tree_rss(pid, procs))
            running[pid] = (k, m, est, t0, p, peak)
            if p.poll() is not None:
                out = open(f'/tmp/claude-0/logs/jobs/{m}.out').read()
                st = 'ok' if p.returncode == 0 else f'FAIL({p.returncode})'
                with open(log, 'a') as f:
                    f.write(f'{time.strftime("%H:%M:%S")} {m} {st} {time.time() - t0:.0f}s peak={peak // 1024}MB\n')
                    if p.returncode != 0:
                        f.write(out[-3000:] + '\n')
                finished.add(k)
                del running[pid]
        items = parse(qpath)
        first = next((j for j, it in enumerate(items) if type(it) is tuple and j not in finished), len(items))
        for k, it in enumerate(items):
            if it in ('--', 'END'):
                if first < k:
                    break
                if it == 'END':
                    return
                continue
            if k in started:
                continue
            m, est = it
            used = sum(r[2] for r in running.values())
            if running and (used + est > budget or len(running) >= maxjobs):
                continue
            fo = open(f'/tmp/claude-0/logs/jobs/{m}.out', 'w')
            if m.startswith('!'):
                # direct `lean` run: no lake startup or trace check (the module's imports must be built already)
                rel = m[1:].replace('.', '/')
                out = f'.lake/build/lib/lean/{rel}'
                os.makedirs(os.path.dirname(out), exist_ok=True)
                cmd = ['lean', f'{rel}.lean', '-o', f'{out}.olean', '-i', f'{out}.ilean']
                p = subprocess.Popen(cmd, stdout=fo, stderr=subprocess.STDOUT, text=True, env=LENV)
            else:
                p = subprocess.Popen(['lake', 'build', m], stdout=fo, stderr=subprocess.STDOUT, text=True, env=ENV)
            running[p.pid] = (k, m, est, time.time(), p, 0)
            started.add(k)
        time.sleep(1)


if __name__ == '__main__':
    main()
