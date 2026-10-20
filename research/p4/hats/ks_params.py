"""Parameters (t1..t5) of the elements x_{r1}(t1)...x_{r5}(t5) of U_v that fix the Hermitian spread S, and of those
that also fix the chosen blocks E (the group K). For fitting formulas valid for all q.  python3 ks_params.py q"""
import itertools
import sys

import numpy as np

src = open('whisk_sym2.py').read()
cut = src.index('def U_elements')
exec(src[:cut].replace("q, secs = int(sys.argv[1]), float(sys.argv[2])", "q, secs = int(sys.argv[1]), 0"))


def U_params():
    for ts in itertools.product(range(q), repeat=5):
        g = ident
        for p, t in zip(rad, ts):
            if t:
                ep, el = elem[(p, t)]
                g = (ep[g[0]], el[g[1]])
        yield ts, g


c = q - 1  # find the hyperplane X0 + c X4 = 0 with -c a non-square
sq = {(x * x) % q for x in range(1, q)}
c = next(c for c in range(1, q) if (-c) % q not in sq)
a = (1, 0, 0, 0, c, 0, 0)
inH = (np.array(P) @ np.array(a)) % q == 0
Sc = np.nonzero(inH[L].all(axis=1))[0]
assert v in Sc and len(Sc) == q ** 3 + 1
Smask = np.zeros(N, bool)
Smask[Sc] = True
print('radical roots:', rad)
print('coefficients:', [coef[p] for p in rad])
KS = [(ts, g) for ts, g in U_params() if Smask[g[1][Sc]].all()]
print(f'hyperplane {a}: |K_S| = {len(KS)}')
for ts, _ in KS[:60]:
    print(ts)
