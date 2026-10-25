"""Copy the Z_M2 voltages of a solved quotient base (same structure: same edge list and C-parts) into a base with a
larger M2, to seed annealing at the next M.  usage: reseed.py solved.txt target.txt out.txt"""
import sys
a = open(sys.argv[1]).read().split('\n')
b = open(sys.argv[2]).read().split('\n')
ha, hb = a[0].split(), b[0].split()
assert ha[0] == hb[0] and ha[1] == hb[1] and ha[3] == hb[3]
out = [b[0]]
for la, lb in zip(a[1:], b[1:]):
    if not la.strip():
        continue
    ua, va, aa, ba = la.split(); ub, vb, ab, bb = lb.split()
    assert (ua, va, aa) == (ub, vb, ab)
    out.append(f'{ub} {vb} {ab} {ba}')
open(sys.argv[3], 'w').write('\n'.join(out) + '\n')
