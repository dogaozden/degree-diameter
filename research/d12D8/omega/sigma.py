"""A pairing sigma: points -> lines for reading 1 of omega.c.  modes: id (sigma(t)=t), rand SEED (random bijection),
singer (equivariant under the first automorphism in HAUT: orbit representatives paired in order, extended by the map).
usage: sigma.py HEX MODE OUT [HAUT.npy | SEED]"""
import sys, numpy as np
f = open(sys.argv[1]); q, n, nl = map(int, f.readline().split()); f.close()
mode = sys.argv[2]
if mode == 'id': s = np.arange(n)
elif mode == 'rand': s = np.random.default_rng(int(sys.argv[4])).permutation(n)
else:
    h = np.load(sys.argv[4])[0]; hp, hl = h[:n], h[n:] - n
    def orbits(perm):
        seen = np.zeros(n, bool); orbs = []
        for x in range(n):
            if seen[x]: continue
            o = [x]; seen[x] = True; y = perm[x]
            while y != x: o.append(y); seen[y] = True; y = perm[y]
            orbs.append(o)
        return orbs
    op, ol = orbits(hp), orbits(hl)
    assert len(op) == len(ol) and len({len(o) for o in op + ol}) == 1, "not semiregular"
    s = np.empty(n, dtype=np.int64)
    for a, b in zip(op, ol):
        for x, y in zip(a, b): s[x] = y
    assert (s[hp] == hl[s]).all()
    print("orbits", len(op), "of size", len(op[0]))
np.savetxt(sys.argv[3], s, fmt="%d")
