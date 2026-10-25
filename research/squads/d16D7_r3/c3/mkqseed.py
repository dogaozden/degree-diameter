#!/usr/bin/env python3
"""mkqseed.py SEED MAP OUT: map an orbit-graph set (one index per line) to quotient vertex ids (one per line).
Every quotient vertex it touches must be fully covered by the set (the seed is F-invariant), else it stops."""
import sys
mp = [list(map(int, l.split())) for l in open(sys.argv[2])]
owner = {}
for q, mem in enumerate(mp):
    for v in mem:
        owner[v] = q
seed = [int(x) for x in open(sys.argv[1]) if x.strip()]
hit = {}
for v in seed:
    hit.setdefault(owner[v], set()).add(v)
for q, vs in hit.items():
    assert vs == set(mp[q]), 'seed not a union of quotient orbits at %d' % q
out = sorted(hit)
open(sys.argv[3], 'w').write('\n'.join(map(str, out)) + '\n')
print(len(out), 'quotient vertices, weight', sum(len(mp[q]) for q in out))
