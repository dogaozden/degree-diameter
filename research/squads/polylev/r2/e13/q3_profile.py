"""q=3: distance profile of the non-pencil dominating 4-sets containing line 0 (concurrent pairs = distance 2)."""
import numpy as np
from collections import Counter
from common import *
H = load(3)
S4 = np.load('q3_nonpencil_containing0.npy')
Lpts = [set(H.lines[l].tolist()) for l in range(H.L)]
prof = Counter()
for s in S4:
    s = [int(x) for x in s]
    d = []
    for a in range(4):
        for b in range(a + 1, 4):
            d.append(2 if Lpts[s[a]] & Lpts[s[b]] else 4)
    prof[tuple(sorted(d))] += 1
print('pairwise line distances (2 = concurrent, 4 = skew-non-opposite), profile counts over the 36 sets:', dict(prof))
