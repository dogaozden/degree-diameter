"""Baseline: plain random lift of H(q)+2 random hop matchings (no symmetry), base 2N vertices, group Z_M.
usage: randbase.py q M seed out.txt"""
import sys, random
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d8')
import gh
q, M, seed, OUT = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
rng = random.Random(seed)
H = gh.load(q); N = H.N
flags = [(int(p), N + k) for k in range(N) for p in H.lines[k]]
inc = set(flags)
hops = []
for m in range(2):
    while True:
        perm = list(range(N)); rng.shuffle(perm)
        ok = all((x, N + perm[x]) not in inc and not any((x, N + perm[x]) in set(hh) for hh in hops) for x in range(N))
        if ok:
            hops.append([(x, N + perm[x]) for x in range(N)]); break
edges = flags + hops[0] + hops[1]
with open(OUT, 'w') as fh:
    fh.write(f'{2*N} {M} 1 {len(edges)}\n')
    for u, v in edges:
        fh.write(f'{u} {v} {rng.randrange(M)} 0\n')
print('wrote', OUT, 'edges', len(edges))
