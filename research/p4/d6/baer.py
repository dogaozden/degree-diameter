"""The q^2 blocks through v of the Hermitian-spread unital carry an affine plane AG(2,q) (inversive plane derived
at v): blocks x, y, z through v are 'collinear' iff no block avoiding v meets all three. Writes B files: the
spread lines of the q blocks through v on one affine line (plus v). Usage: baer.py q seed nfiles"""
import collections, itertools, sys
from bstruct import unital

q, seed, nf = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
S, lines, spt, sl, blocks = unital(q, seed)
v = S[0]
thru = [b for b in blocks if v in b]
idx = {}
for i, b in enumerate(thru):
    for s in b:
        if s != v:
            idx[s] = i
circles = set()
for c in blocks:
    if v not in c:
        circles.add(frozenset(idx[s] for s in c))
print('blocks through v', len(thru), 'circles', len(circles))
cover = collections.defaultdict(set)   # pair -> thirds on a common circle
for C in circles:
    for x, y in itertools.combinations(sorted(C), 2):
        cover[(x, y)] |= C
n = len(thru)
alines = set()
for x, y in itertools.combinations(range(n), 2):
    Lxy = frozenset(z for z in range(n) if z not in cover[(x, y)] or z in (x, y))
    alines.add(Lxy)
print('affine lines', len(alines), collections.Counter(len(l) for l in alines))
for k, Lxy in enumerate(sorted(alines, key=sorted)[:nf]):
    B = sorted(set(s for i in Lxy for s in thru[i]))
    open(f'runs/B_q{q}_line{k}.txt', 'w').write('\n'.join(map(str, B)) + '\n')
