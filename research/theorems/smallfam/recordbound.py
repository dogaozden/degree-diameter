"""Fibre bound at the record's own j-pattern: B_j = k * min_J |W_J| for a given (DELTA, D, k, o, j), compared with N.
Usage: python3 recordbound.py DELTA D k o j1 j2 ... [--N N]"""
import sys, time
import cyclobound
cyclobound.FIBER = True
a = sys.argv[1:]
N = None
if '--N' in a:
    i = a.index('--N'); N = int(a[i + 1]); a = a[:i] + a[i + 2:]
Delta, D, k, o = map(int, a[:4])
j = tuple([0] + list(map(int, a[4:])))
t = time.time()
B = cyclobound.ball_bound(Delta, D, k, o, j)
print(f'Delta={Delta} D={D} k={k} o={o} j={j}: B_j = k*min_J|W_J| = {B}' + (f'; N = {N}, N/B_j = {N / B:.3f}' if N else '')
      + f'  ({time.time() - t:.0f} s)', flush=True)
