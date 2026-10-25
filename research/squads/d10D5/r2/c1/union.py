#!/usr/bin/env python3
"""union.py GQBIN SEED TRIES FEASFILE [MINK]: random greedy unions of feasible single flag orbits (disjoint points and
lines, exact-coverage perfect matching at every step, sym.Matcher). Prints the best union found, with the number of
collinear point pairs and concurrent line pairs (these relax the hub-graph tournament). Writes union_SEED.txt.
usage: python3 -I union.py gq/gq_q7.bin SEED TRIES feas_5_4.txt"""
import sys, random, time
sys.path.insert(0, '.')
from sym import *
fn = sys.argv[1]; seed = int(sys.argv[2]); tries = int(sys.argv[3]); feasf = sys.argv[4]
rng = random.Random(seed)
q, N, lines, lof, coords = load_all(fn)
Mt = Matcher(q, N, lines, lof)
orbs = []
for ln in open(feasf):
    fl = [tuple(map(int, t.split(':'))) for t in ln.split()]
    if fl: orbs.append(fl)
# dedupe
uniq = {}
for ob in orbs: uniq[tuple(sorted(ob))] = ob
orbs = list(uniq.values())
print('feasible single orbits', len(orbs), 'sizes', sorted({len(o) for o in orbs}), flush=True)
def pairs_info(flags):
    col = 0; conc = 0
    for i in range(len(flags)):
        for j in range(i + 1, len(flags)):
            p, l = flags[i]; p2, l2 = flags[j]
            if (Mt.Pm[p] >> p2) & 1 and p2 != p: col += 1
            if (Mt.Lm[l] >> l2) & 1 and l2 != l: conc += 1
    return col, conc
best = []; bestk = 0
t0 = time.time(); tests = 0
for t in range(tries):
    order = list(range(len(orbs))); rng.shuffle(order)
    cur = []; FP = set(); FL = set()
    for oi in order:
        ob = orbs[oi]; ps = {p for p, _ in ob}; ls = {l for _, l in ob}
        if ps & FP or ls & FL: continue
        cand = cur + ob
        sz, _ = Mt.size(cand); tests += 1
        if sz == N:
            cur = cand; FP |= ps; FL |= ls
    if len(cur) > bestk:
        bestk = len(cur); best = cur
        print('try', t, 'k', len(cur), 'collinear/concurrent pairs', pairs_info(cur), 'time %.1f' % (time.time() - t0), flush=True)
print('BEST k', bestk, 'tests', tests, 'flags', ' '.join(f'{p}:{l}' for p, l in best), flush=True)
with open(f'union_{seed}.txt', 'w') as f: f.write(' '.join(f'{p}:{l}' for p, l in best) + '\n')
