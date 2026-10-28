"""Sample the full stabiliser Aut_S (order 3542880, from autS_gens.json) by product replacement and collect one
representative of each conjugacy class (invariant: cycle type on points and on lines) of subgroups of prime order.
Every nontrivial group of collineations contains a subgroup of prime order, and a set invariant under a group is
invariant under each of its subgroups, so the max over prime-order subgroups bounds every symmetric construction."""
import json, random, math, collections, numpy as np
D = '/home/user/degree-diameter/research/squads/gqd5-r2/c2/'
S_ = json.load(open(D + 'struct.json'))
lines, plines, S = S_['lines'], S_['plines'], set(S_['S'])
npts, nl = len(plines), len(lines)
gens = [np.array(p, dtype=np.int32) for p in json.load(open('autS_gens.json'))]
line_index = {frozenset(l): i for i, l in enumerate(lines)}
S_list = sorted({int(x) for x in S_['sline']})
sline = np.array(S_['sline']); sidx = {L: i for i, L in enumerate(S_list)}
sl_of = np.array([sidx[int(x)] for x in sline])
def fixed_S(g):
    f = np.full(len(S_list), -1)
    f[sl_of] = sl_of[g]
    return int(np.sum(f == np.arange(len(S_list))))
def cycles(p):
    n = len(p); seen = np.zeros(n, bool); out = []
    for s in range(n):
        if seen[s]: continue
        c = 0; x = s
        while not seen[x]:
            seen[x] = True; x = p[x]; c += 1
        out.append(c)
    return out
def ctype(p):
    return tuple(sorted(collections.Counter(cycles(p)).items()))
def order(p):
    return math.lcm(*cycles(p)) if len(p) else 1
def power(p, k):
    r = np.arange(len(p), dtype=np.int32); b = p.copy()
    while k:
        if k & 1: r = b[r]
        b = b[b]; k >>= 1
    return r
random.seed(12345)
state = [g.copy() for g in gens] * 2
for _ in range(50): state.append(gens[random.randrange(len(gens))].copy())
def step():
    i, j = random.sample(range(len(state)), 2)
    state[i] = state[i][state[j]]
    return state[i]
for _ in range(200): step()
reps = {}   # invariant -> (order, element)
samples = 0
primes = [2, 3, 5, 11, 61]
need = set(primes)
while samples < 6000:
    g = step(); samples += 1
    o = order(g)
    for p in primes:
        if o % p == 0:
            h = power(g, o // p)
            inv = (p, ctype(h), fixed_S(h))
            if inv not in reps:
                reps[inv] = h
                print('new class: order', p, 'pt cycles', dict(collections.Counter(cycles(h))),
                      'fixed S-lines', inv[2], flush=True)
                json.dump([{'order': k[0], 'ptype': [list(x) for x in k[1]], 'fixedS': k[2]} for k in reps],
                          open('prime_classes_partial.json', 'w'))
print('samples', samples, 'classes', len(reps), flush=True)
out = []
for k, (inv, h) in enumerate(reps.items()):
    out.append({'order': inv[0], 'perm': h.tolist(), 'ptype': [list(x) for x in inv[1]], 'fixedS': inv[2]})
json.dump(out, open('prime_reps.json', 'w'))
