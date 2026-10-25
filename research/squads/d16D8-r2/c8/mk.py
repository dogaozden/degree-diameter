# c8 wildcard generator: W(q) base variants for baselift (imports the shared gq.py read-only).
import sys, random
sys.path.insert(0, '/home/user/degree-diameter/research/d16D8')
import gq
# usage: mk.py q m seed mode OUT
#   mode 'std'  : flags cls1 random voltages, matchings cls100/101 random (same as gq.random_design)
#   mode 'mzero': flags fixed at voltage 0 (cls0), matchings carry all voltage (cls100/101)
#   mode 'fzero': matchings fixed at voltage 0 (cls0), flags carry all voltage (cls1)
q, m, seed, mode, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4], sys.argv[5]
G = gq.load(q); N = G['N']; rnd = random.Random(seed)
edges = []
for l, L in enumerate(G['lines']):
    for p in L:
        cls = 0 if mode == 'mzero' else 1
        edges.append((p, N + l, 0 if mode == 'mzero' else rnd.randrange(m), cls))
for k in range(2):
    perm = list(range(N)); rnd.shuffle(perm)
    for p in range(N):
        cls = 0 if mode == 'fzero' else 100 + k
        edges.append((p, N + perm[p], 0 if mode == 'fzero' else rnd.randrange(m), cls))
gq.write_base(out, 2 * N, m, edges)
print('wrote', out, 'V', 2 * N, 'm', m, 'E', len(edges))
