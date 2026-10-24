"""j-patterns of the Delta=3 Frobenius/affine solutions, up to affine maps of Z_k: is the pattern an arithmetic progression
with the translation on the middle element, i.e. S ~ {(0,0), (1,d), (0,2d)}?  Reads runs/frob_d3D*/ and runs/affq_d3D*/."""
import glob, os, re
from math import gcd
def classify(k, js, a_pos):
    # js: j-parts of the three elements; a_pos: index of the element with nonzero a-part
    out = []
    for (i, j) in [(0,1),(0,2),(1,2)]:
        pass
    J = sorted(set(js))
    ap = any((2*js[b] - js[a] - js[c]) % k == 0 for (a, b, c) in [(0,1,2),(1,0,2),(2,0,1)])
    mid = None
    for (a, b, c) in [(0,1,2),(1,0,2),(2,0,1)]:
        if (2*js[a] - js[b] - js[c]) % k == 0:
            mid = a
    return ap, mid == a_pos
tot = {}
for f in sorted(glob.glob('runs/frob_d3D*/*.txt') + glob.glob('runs/affq_d3D*/*.txt')):
    D = int(re.search(r'D(\d+)', f).group(1))
    hdr = open(f).readline()
    k = int(re.search(r'Z_(\d+) \(ord|x\| C_(\d+)', hdr).group(1) or re.search(r'C_(\d+)', hdr).group(1)) if 'Z_' in hdr and 'C_' not in hdr else None
    m = re.search(r'G=Z_(\d+) x\|_(\d+) Z_(\d+)', hdr)
    if m:
        k = int(m.group(3))
    else:
        k = int(re.search(r'C_(\d+),', hdr).group(1))
    res = []
    for line in open(f):
        if not line.startswith('SOL'): continue
        s = list(map(int, line.split()[1:]))
        els = [divmod(x, k) for x in s]
        js = [j for a, j in els]
        a_pos = [i for i, (a, j) in enumerate(els) if a != 0]
        ap, midtrans = classify(k, js, a_pos[0] if len(a_pos) == 1 else -1)
        res.append((ap, midtrans, len(a_pos)))
    print(D, os.path.basename(f), 'k', k, 'solutions', len(res), 'AP', sum(r[0] for r in res), 'AP with translation in the middle', sum(r[1] for r in res))
