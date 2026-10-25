import sys, collections
sys.dont_write_bytecode = True
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D5/r3/c4')
from cov import N, PM, LM, read_sol, dists, bfs_all
name = sys.argv[1]
S = read_sol(name); F = S['F']; sig = S['sig']; k = len(F); Fset = set(F); Lset = set(sig[p] for p in F)
adj, nv = bfs_all(F, sig, S['mv0'], S['mv1'], S['nu'], S['pairs'], S['H'])
base = 6 * 2 * N
def stype(v):
    if v >= base: return 'hub'
    x, h = divmod(v, 6)
    if x < N: return 'P' + ('F' if x in Fset else '')
    return 'L' + ('F' if (x - N) in Lset else '')
cnt = collections.Counter(); ex = {}
sources = [6 * v for v in range(2 * N)] + list(range(base, nv))
for s in sources:
    d = dists(adj, s)
    for t in range(nv):
        if t != s and (d[t] < 0 or d[t] > 5):
            key = (stype(s), stype(t), (t % 6) % 3 if t < base else '-')
            cnt[key] += 1
            ex.setdefault(key, (s, t))
for key, c in sorted(cnt.items(), key=lambda z: -z[1]):
    s, t = ex[key]
    print('source', key[0], 'target', key[1], 'coset(h mod 3)', key[2], 'count', c, 'example src', s, 'tgt', t)
print('total', sum(cnt.values()))
