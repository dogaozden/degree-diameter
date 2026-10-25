#!/usr/bin/env python3
"""Watch a poolq log and print the axioms of every generated record as soon as its Record module is built
(run from lean/).

usage: axwatch.py LOG [LOG ...] [--skip CELL,CELL,...]
For each `... <Module>.Record ok` line of a generated cell (`LeanAll/Haar*`), runs `#print axioms` on the cell's
`nb_*` theorem and appends the result to axioms_big.txt (once per cell). Cells in --skip are left out (bigcell.py
checks its own cells). Stops when /tmp/claude-0/logs/axwatch.stop exists."""
import os, re, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
ENV = dict(os.environ)
ENV['PATH'] = os.path.expanduser('~/.elan/bin') + ':' + ENV['PATH']
OUT = os.path.join(HERE, 'axioms_big.txt')


def done_cells():
    if not os.path.exists(OUT):
        return set()
    return {l.split()[0] for l in open(OUT) if l.strip()}


def check(cell):
    rec = f'BipartiteDD/LeanAll/{cell}/Record.lean'
    m = re.search(r'^theorem (nb_\w+)', open(rec).read(), re.M)
    thm = m.group(1)
    tf = f'/tmp/claude-0/work/ax/{cell}.lean'
    os.makedirs(os.path.dirname(tf), exist_ok=True)
    open(tf, 'w').write(f'import BipartiteDD.LeanAll.{cell}.Record\n#print axioms {thm}\n#check @{thm}\n')
    r = subprocess.run(['lake', 'env', 'lean', tf], capture_output=True, text=True, env=ENV)
    out = ' | '.join(l.strip() for l in (r.stdout + r.stderr).strip().split('\n'))
    with open(OUT, 'a') as f:
        f.write(f'{cell} ({time.strftime("%Y-%m-%d %H:%M")}): {out}\n')
    print(cell, out, flush=True)


def main():
    args = sys.argv[1:]
    skip = set()
    if '--skip' in args:
        i = args.index('--skip')
        skip = set(args[i + 1].split(','))
        args = args[:i] + args[i + 2:]
    logs = args
    while not os.path.exists('/tmp/claude-0/logs/axwatch.stop'):
        seen = done_cells() | skip
        for lg in logs:
            if not os.path.exists(lg):
                continue
            for l in open(lg):
                m = re.match(r'\d\d:\d\d:\d\d !?BipartiteDD\.LeanAll\.(Haar\w+)\.Record ok', l)
                if m and m.group(1) not in seen:
                    check(m.group(1))
                    seen.add(m.group(1))
        time.sleep(30)


if __name__ == '__main__':
    main()
