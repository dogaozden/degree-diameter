#!/usr/bin/env python3
"""End-to-end completeness check of the coset-pattern search (hunt-d5) on a small group, at Delta = 5:
brute force (`haar5 exhp`, all S ∋ e) versus `haar5 prod` over all pattern classes (jpatterns.py + jexact.py).
The set of pattern classes containing a cost-0 set must be the same both ways.

Usage: jcheck.py p k r n DIR      (writes its files in DIR)
"""
import os, subprocess, sys
p, k, r, n = map(int, sys.argv[1:5]); D = sys.argv[5]; os.makedirs(D, exist_ok=True)
T = os.path.dirname(os.path.abspath(__file__)); run = lambda *a: subprocess.run(list(a), capture_output=True, text=True).stdout
tab = f'{D}/t.bin'; run('python3', f'{T}/metatab.py', str(p), str(k), str(r), tab, str(n))
exh = run(f'{T}/haar5', 'exhp', tab, '5', '0')
pat = run('python3', f'{T}/jpatterns.py', '5', str(p), str(k), str(r), str(n), '100000'); open(f'{D}/pat.txt', 'w').write(pat)
run('python3', f'{T}/jexact.py', '5', str(p), str(k), str(r), str(n), f'{D}/pat.txt', f'{D}/l.lists')
prod = run(f'{T}/haar5', 'prod', tab, '5', f'{D}/l.lists', '0')
def key_of(pts):
    keys = []
    for s in (1, -1):
        q = [((s * j) % k, (s * z) % n) for j, z in pts]
        for j0, z0 in set(q): keys.append(tuple(sorted(((j - j0) % k, (z - z0) % n) for j, z in q)))
    return min(keys)
cls = {}
for l in pat.split('\n'):
    if l and not l.startswith('#'): cls[tuple(tuple(map(int, t.split(','))) for t in l.split()[1:])] = len(cls)
a = {}
for l in exh.split('\n'):
    if l.startswith('cost 0'):
        S = list(map(int, l.split()[3:])); c = cls.get(key_of([((x // n) % k, x % n) for x in S]), -1); a[c] = a.get(c, 0) + 1
b = {int(l.split()[1]) for l in prod.split('\n') if l.startswith('BLOCK') and l.rstrip().endswith(' min=0')}
print(f'group meta {p} {k} {r} x Z{n} (N = {p * k * n}), d = 5: {sum(a.values())} cost-0 sets by brute force in classes',
      sorted(a), f'of {len(cls)}; prod found cost 0 in classes', sorted(b), '->', 'MATCH' if set(a) == b else 'MISMATCH')
