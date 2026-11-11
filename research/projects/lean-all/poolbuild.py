#!/usr/bin/env python3
"""Run `lake build MOD` jobs in parallel under a memory budget (run from lean/).

usage: poolbuild.py LOG BUDGET_GB MAXJOBS JOB [JOB ...]
A JOB is MOD:GB (estimated peak memory) or a barrier '--' (wait for everything before it). Jobs start in order
when the running estimates plus theirs fit the budget. Each finished job logs wall time, measured peak RSS and status;
a failure is logged with the tail of its output and the rest still runs."""
import os, subprocess, sys, time

ENV = dict(os.environ)
ENV['PATH'] = os.path.expanduser('~/.elan/bin') + ':' + ENV['PATH']


def lean_rss_by_ppid():
    """RSS (kB) of each lean process, keyed by the pid of its lake parent chain root we started."""
    out = {}
    for pid in os.listdir('/proc'):
        if not pid.isdigit():
            continue
        try:
            with open(f'/proc/{pid}/stat') as f:
                st = f.read().split()
            comm = st[1]
            ppid = int(st[3])
            rss = 0
            with open(f'/proc/{pid}/status') as f:
                for line in f:
                    if line.startswith('VmRSS:'):
                        rss = int(line.split()[1])
            out[int(pid)] = (comm, ppid, rss)
        except OSError:
            pass
    return out


def tree_rss(root, procs):
    tot = 0
    stack = [root]
    seen = set()
    while stack:
        p = stack.pop()
        if p in seen:
            continue
        seen.add(p)
        for q, (comm, ppid, rss) in procs.items():
            if ppid == p:
                stack.append(q)
                if comm == '(lean)':
                    tot += rss
    return tot


def main():
    log, budget, maxjobs = sys.argv[1], float(sys.argv[2]), int(sys.argv[3])
    jobs = sys.argv[4:]
    queue = []
    for j in jobs:
        if j == '--':
            queue.append(None)
        else:
            m, g = j.rsplit(':', 1)
            queue.append((m, float(g)))
    running = {}  # pid -> (mod, est, t0, popen, peak)
    i = 0
    while i < len(queue) or running:
        procs = lean_rss_by_ppid()
        for pid, (m, est, t0, p, peak) in list(running.items()):
            rss = tree_rss(pid, procs)
            peak = max(peak, rss)
            running[pid] = (m, est, t0, p, peak)
            if p.poll() is not None:
                out = open(f'/tmp/claude-0/logs/jobs/{m}.out').read()
                st = 'ok' if p.returncode == 0 else f'FAIL({p.returncode})'
                with open(log, 'a') as f:
                    f.write(f'{time.strftime("%H:%M:%S")} {m} {st} {time.time() - t0:.0f}s peak={peak // 1024}MB\n')
                    if p.returncode != 0:
                        f.write(out[-3000:] + '\n')
                del running[pid]
        while i < len(queue):
            if queue[i] is None:
                if running:
                    break
                i += 1
                continue
            m, est = queue[i]
            used = sum(r[1] for r in running.values())
            if running and (used + est > budget or len(running) >= maxjobs):
                break
            os.makedirs('/tmp/claude-0/logs/jobs', exist_ok=True)
            fo = open(f'/tmp/claude-0/logs/jobs/{m}.out', 'w')
            p = subprocess.Popen(['lake', 'build', m], stdout=fo, stderr=subprocess.STDOUT, text=True, env=ENV)
            running[p.pid] = (m, est, time.time(), p, 0)
            i += 1
        time.sleep(1)


if __name__ == '__main__':
    main()
