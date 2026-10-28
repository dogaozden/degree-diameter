"""grporb.py: point orbits of cyclic collineation groups of H(q) of prescribed orders (random elements of G2(q) built as
in g2.py, powered down to the wanted order). Writes OUT_o{order}_{i}.porb (int32 orbit id per point)
and OUT_o{order}_{i}.pperm (int32 image of each point under the generator), OUT_o{order}_{i}.h.txt (the 7x7 matrix).
Usage: python3 grporb.py HEXBIN OUTPREFIX SEED order [order ...]"""
import sys
sys.path.insert(0, '..')
import numpy as np
from hexlib import Hex
from g2 import F7, random_apartment, apartment_map, proj_order, factor


def main():
    H = Hex(sys.argv[1]); out = sys.argv[2]; rng = np.random.default_rng(int(sys.argv[3]))
    wanted = [int(x) for x in sys.argv[4:]]
    H.bfs(0)
    q = H.q
    F = F7(H)
    gens = []
    while len(gens) < 2:
        g = apartment_map(H, random_apartment(H, rng), rng)
        if g is not None:
            gens.append(g)
    E = q ** 6 * (q ** 6 - 1) * (q ** 2 - 1) * (q - 1)
    found = {w: 0 for w in wanted}
    for trial in range(600):
        if all(found[w] >= 2 for w in wanted):
            break
        g = np.eye(7, dtype=np.int64)
        for b in rng.integers(0, 2, size=8):
            g = F.mul(g, gens[b])
        o = proj_order(F, g, E)
        for w in wanted:
            if found[w] >= 2 or o % w:
                continue
            h = F.pw(g, o // w)
            pm = H.point_ids(H.matvec(h, H.coord))
            orb = -np.ones(H.N, dtype=np.int64)
            no = 0
            for s in range(H.N):
                if orb[s] >= 0:
                    continue
                x = s
                while orb[x] < 0:
                    orb[x] = no
                    x = pm[x]
                no += 1
            sizes = np.bincount(np.bincount(orb))
            fn = f'{out}_o{w}_{found[w]}.porb'
            orb.astype(np.int32).tofile(fn)
            pm.astype(np.int32).tofile(fn[:-5] + '.pperm')
            np.savetxt(fn[:-5] + '.h.txt', h, fmt='%d')
            print(f'order {w}: {no} orbits, orbit-size histogram {dict((i, int(c)) for i, c in enumerate(sizes) if c)} -> {fn}', flush=True)
            found[w] += 1


if __name__ == '__main__':
    main()
