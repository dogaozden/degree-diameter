import sys, random
sys.path.insert(0, '.')
from sym import *
rng = random.Random(11)
q, N, lines, lof, coords = load_all('gq/gq_q7.bin')
index = {c: i for i, c in enumerate(coords)}
lidx = {frozenset(ps): l for l, ps in enumerate(lines)}
Mt = Matcher(q, N, lines, lof)
flags_all = [(p, l) for l in range(len(lines)) for p in lines[l]]
from gq import perp, lperp
for e in range(200000):
    Mx = random_elem(rng)
    pp = perm_points(Mx, coords, index); ct = cycle_type(pp)
    if order_of(ct) == 8 and ct == {8: N // 8}: break
pl = perm_lines(pp, lines, lidx)
orbs = flag_orbits(pp, pl, flags_all)
Pmask = [set(perp(lines, lof, p)) for p in range(N)]
Lset = [set(lperp(lines, lof, l)) for l in range(N)]
res = []
for oi, ob in enumerate(orbs):
    sz, _ = Mt.size(ob)
    if sz != N: continue
    cp = sum(1 for i in range(8) for j in range(i) if ob[j][0] in Pmask[ob[i][0]])
    cl = sum(1 for i in range(8) for j in range(i) if ob[j][1] in Lset[ob[i][1]])
    res.append((cp + cl, cp, cl, ob))
res.sort(key=lambda t: -t[0])
print('feasible single orbits', len(res))
for s, cp, cl, ob in res: print('collinear_pts', cp, 'concurrent_lines', cl, 'flags', ' '.join(f'{p}:{l}' for p, l in ob))
