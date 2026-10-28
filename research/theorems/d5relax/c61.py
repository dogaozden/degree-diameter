"""Orbits of a cyclic subgroup of order (q^2+1)/2 of Sp(4,q) on W(q) and the best relaxed union (job d5-relax).
usage: python3 c61.py q seed"""
import sys, random, numpy as np
from orbits import WSp, orbits_of, perm_order, best_union, Wq_pow, check_relaxed
q = int(sys.argv[1]); rng = random.Random(int(sys.argv[2])); W = WSp(q); m = (q * q + 1) // 2
sp = list(map(int, open('data/W%d_spread.txt' % q).read().split()))
found = 0
for e in range(400):
    g = W.random_element(rng); o = perm_order(g)
    if o % m: continue
    h = Wq_pow(g, o // m); lab, k = orbits_of([h], W.n)
    sizes = np.bincount(lab)
    # does <h> fix the regular spread of Lemma 1.1?  (spread line of h(x) depends only on spread line of x)
    img = {}
    fix = all(img.setdefault(sp[x], sp[int(h[x])]) == sp[int(h[x])] for x in range(W.n))
    s, T = best_union(W, lab, k, timelimit=120)
    print('elt %d order %d: <g^%d> of order %d, %d orbits (sizes %s), stabilises the spread: %s, best relaxed union %d'
          % (e, o, o // m, m, k, sorted(set(sizes.tolist())), fix, s)); sys.stdout.flush()
    found += 1
    if found >= 6: break
