#!/usr/bin/env python3
"""Collect near-miss Haar sets for Z53 x| Z26 (n = 1, d = 9) from hunt-d5 files; check cost with haar5 and pfill;
print the canonical j-pattern of each set with cost <= LIM. usage: collect.py LIM"""
import subprocess, sys, os
LIM = int(sys.argv[1]) if len(sys.argv) > 1 else 4
ROOT = '/home/user/degree-diameter/research/squads/hunt-d5'
T = ROOT + '/tables/mt_53_26_16.bin'
files = [l.strip() for l in open('files.txt') if l.strip()]
sets = []
for f in files:
    p = os.path.join(ROOT, f)
    L = open(p).read().split('\n')
    hdr = L[0].split()
    if hdr[:9] != ['9','5','meta','53','26','16','n','1','N'] or len(L) < 10:
        continue
    idx = [int(l.split()[0]) for l in L[1:10] if l.strip()]
    if len(idx) != 9: continue
    sets.append((f, idx))
inp = '\n'.join(' '.join(map(str, s)) for _, s in sets) + '\n'
out = subprocess.run(['nice','-n','10','timeout','120', ROOT + '/tools/haar5', 'eval', T, '9'], input=inp, capture_output=True, text=True).stdout.split()
pat = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'pfill')
out2 = subprocess.run(['nice','-n','10','timeout','120', pat, T, '9','1','0','1','1','eval'], input=inp, capture_output=True, text=True).stdout.split()
assert len(out) == len(sets) == len(out2), (len(out), len(out2), len(sets))
res = []
for (f, s), c1, c2 in zip(sets, out, out2):
    assert c1 == c2, (f, c1, c2)
    c = int(c1)
    if c > LIM: continue
    # canonical pattern: shift so that each element can be the identity, sorted j-multiset, lexicographic minimum
    best = None
    for e in s:
        je = e % 26
        pt = tuple(sorted(((x % 26) - je) % 26 for x in s))
        if best is None or pt < best: best = pt
    res.append((c, best, f, s))
res.sort()
for c, pt, f, s in res:
    print(c, ','.join(map(str, pt)), f, ' '.join(map(str, s)))
print('total_sets', len(sets), 'cost<=%d' % LIM, len(res), file=sys.stderr)
