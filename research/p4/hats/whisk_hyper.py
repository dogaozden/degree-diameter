"""Do the whiskers of an exact solution lie in a few hyperplanes of PG(6,q)? Count, for every hyperplane,
how many whiskers, S-lines and H(q)-lines it contains.  python3 whisk_hyper.py q"""
import itertools
import json
import sys
from collections import Counter

sys.argv = [sys.argv[0], sys.argv[1], 'none', '1']
src = open('whisk_ansatz.py').read().split('def solve')[0]
exec(src)
d = json.load(open(f'whiskers_ansatz_q{q}.json'))
W = d['whiskers']
E = set(s for B in d['blocks_v'] for s in B) - {v}
best = []
for a in itertools.product(range(q), repeat=7):
    if not any(a) or next(c for c in a if c) != 1:
        continue
    inH = [sum(x * y for x, y in zip(a, w)) % q == 0 for w in P]
    nw = sum(1 for k in W if all(inH[p] for p in lines[k]))
    if nw >= 2:
        ns = sum(1 for k in S if all(inH[p] for p in lines[k]))
        nE = sum(1 for k in E if all(inH[p] for p in lines[k]))
        nall = sum(1 for k in range(N) if all(inH[p] for p in lines[k]))
        best.append((nw, ns, nE, all(inH[p] for p in lines[v]), nall, a))
best.sort(reverse=True)
for b in best[:12]:
    print(b)
print('distribution of whisker counts:', sorted(Counter(b[0] for b in best).items()))
