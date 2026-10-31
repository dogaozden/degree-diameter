# augdg.py IN OUT NAB SEED M DMG K: like augment.py, but the removed base edges are drawn from the K lowest-damage
# edges of DMG (file from dmg.py: "cost index edge" lines, sorted by cost). One new pair.
import sys, random
inf, outf, nab, seed, M, dmg, K = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), sys.argv[6], int(sys.argv[7])
rnd = random.Random(seed)
L = open(inf).read().split('\n')
b, E = map(int, L[0].split()[:2]); side = L[1].split()
edges = [list(map(int, l.split()[:3])) if len(l.split()) > 2 else list(map(int, l.split()))+[0] for l in L[2:2+E]]
cand = [int(l.split()[1]) for l in open(dmg).read().strip().split('\n')[:K]]
k = 6 - nab
idx = set(rnd.sample(cand, k))
removed = [edges[i] for i in idx]
keep = [edges[i] for i in range(E) if i not in idx]
fu = [e[0] for e in removed]; fv = [e[1] for e in removed]
rnd.shuffle(fu); rnd.shuffle(fv)
a, bb = b, b + 1
side += [0, 1]
edges = keep + [[a, v, rnd.randrange(M)] for v in fv] + [[u, bb, rnd.randrange(M)] for u in fu] + [[a, bb, rnd.randrange(M)] for _ in range(nab)]
with open(outf, 'w') as f:
    f.write(f"{b+2} {len(edges)}\n" + ' '.join(map(str, side)) + '\n')
    for u, w, t in edges: f.write(f"{u} {w} {t}\n")
