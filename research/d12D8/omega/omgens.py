"""Generator permutations for omega.c graphs, for apsp_auto: the Z_5 rotation (copy 5B+c -> 5B+c+1, new (t,k) -> (t,k+1)),
swaps of two blocks of the same type, and hexagon automorphisms h from haut.py acting on every copy and on the new vertices
((t,k) -> (h(t),k) for points t; reading 2 also needs h on lines for kbar; reading 1 needs h(sigma(t)) = sigma(h(t))).
Every generator is re-checked edge by edge by apsp_auto, so a wrong one is rejected there.
usage: omgens.py HEX TYPES READING HAUT.npy OUT.bin [SIGMA]"""
import sys, numpy as np
f = open(sys.argv[1]); q, n, nl = map(int, f.readline().split()); f.close()
types, reading, H = sys.argv[2], int(sys.argv[3]), np.load(sys.argv[4])
sig = np.loadtxt(sys.argv[6], dtype=np.int64) if len(sys.argv) > 6 else np.arange(n)
N1 = 2 * n; al = len(types); C = 5 * al; base = C * N1; nv = base + 10 * n
cop = np.arange(base).reshape(C, N1); new = np.arange(base, nv).reshape(n, 2, 5)   # new[t, bar, k]
gens = []
# rotation
p = np.arange(nv)
for B in range(al):
    for c in range(5): p[cop[5 * B + c]] = cop[5 * B + (c + 1) % 5]
p[new] = new[:, :, [1, 2, 3, 4, 0]]
gens.append(p)
# swaps of same-type blocks (consecutive pairs in the list of each type)
for ty in 'ab':
    bl = [B for B in range(al) if types[B] == ty]
    for B1, B2 in zip(bl, bl[1:]):
        p = np.arange(nv)
        for c in range(5): p[cop[5 * B1 + c]] = cop[5 * B2 + c]; p[cop[5 * B2 + c]] = cop[5 * B1 + c]
        gens.append(p)
# hexagon automorphisms
for h in H:
    hp, hl = h[:n], h[n:] - n
    if reading == 1 and not (sig[hp] == hl[sig]).all():
        print("skip a hexagon automorphism: it does not commute with sigma"); continue
    p = np.arange(nv)
    for c in range(C): p[cop[c]] = cop[c][h]
    if reading == 1: p[new] = new[hp]
    else:
        p[new[:, 0, :]] = new[hp][:, 0, :]; p[new[:, 1, :]] = new[hl][:, 1, :]
    gens.append(p)
G = np.array(gens, dtype=np.int32)
with open(sys.argv[5], 'wb') as o: np.array([len(G), nv], dtype=np.int32).tofile(o); G.tofile(o)
print(len(G), "generators,", nv, "vertices")
