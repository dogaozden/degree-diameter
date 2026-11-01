# (3) which label multisets (labels of S, e has label 0) reach every coset? lazy support = h-fold sumset of D
import itertools, numpy as np, sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/beyond11b/r2/h17')
from analyse import coset_nb_dp
k, h, d = 19, 5, 4
def lazy_support(labels):
    D = {(y - x) % k for x in labels for y in labels}
    cur = {0}
    for _ in range(h):
        cur = {(a + b) % k for a in cur for b in D}
    return cur
tot = 0; full_lazy = 0; full_nb = 0; by_ell = {}
ok_ell = {}
for rest in itertools.combinations_with_replacement(range(k), d - 1):
    labels = (0,) + rest
    ell = len(set(labels))
    tot += 1
    lz = len(lazy_support(labels)) == k
    nb = bool((coset_nb_dp(list(labels)) > 0).all())
    full_lazy += lz; full_nb += nb
    by_ell.setdefault(ell, [0, 0, 0])
    by_ell[ell][0] += 1; by_ell[ell][1] += lz; by_ell[ell][2] += nb
print('multisets (e has label 0):', tot, ' all-cosets lazy:', full_lazy, ' all-cosets NB:', full_nb)
print('by number of distinct labels: ell: [count, lazy-full, NB-full]', by_ell)
