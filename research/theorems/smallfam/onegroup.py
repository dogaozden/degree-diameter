"""Exhaustive Haar-graph search in ONE SmallGroup (n, i), up to Aut(G): the per-group step of allgroups.py.

Exports the multiplication table, the Aut(G)-reduced plan of (s1, s2) pairs and the abelianization map (hx's quotient
filter), then runs hx over every remaining set. Prints hx's SOL lines and its DONE line.
Usage: SCRATCH=dir python3 onegroup.py n i DELTA D [--threads T] [--maxprint M]
"""
import argparse
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from allgroups import export  # noqa: E402


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('n', type=int)
    ap.add_argument('i', type=int)
    ap.add_argument('Delta', type=int)
    ap.add_argument('D', type=int)
    ap.add_argument('--threads', type=int, default=1)
    ap.add_argument('--maxprint', type=int, default=50)
    ap.add_argument('--gap-timeout', type=int, default=3600)
    a = ap.parse_args()
    ex = export(a.n, a.i, True, a.gap_timeout)
    if ex is None:
        print('gap-timeout'); return
    struct, tab, plan, qmap = ex
    nplan = sum(1 for _ in open(plan))
    print(f'# SmallGroup({a.n},{a.i}) = {struct}; plan lines {nplan}; Delta={a.Delta} D={a.D}', flush=True)
    env = dict(os.environ, THREADS=str(a.threads), QMAP=qmap)
    r = subprocess.run([os.path.join(HERE, 'hx'), 'tab', tab, str(a.Delta), str(a.D), plan, str(a.maxprint)],
                       capture_output=True, text=True, env=env).stdout
    print(r, end='', flush=True)
    for p in (tab, plan, qmap):
        os.remove(p)


if __name__ == '__main__':
    main()
