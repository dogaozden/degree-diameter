#!/usr/bin/env python3
"""pairs.py GQBIN SEED NSEED FEASFILE: for NSEED random feasible order-5 orbits O1, test every disjoint feasible orbit O2
with exact-coverage matching on O1+O2; prints each feasible union (k=10) with collinear/concurrent pair counts.
Appends unions to pairs_SEED.txt (one union per line, flags 'p:l').  usage: python3 -I pairs.py gq/gq_q7.bin SEED NSEED feas_5_4.txt"""
import sys, random, time
sys.path.insert(0, '.')
from sym import *
fn = sys.argv[1]; seed = int(sys.argv[2]); nseed = int(sys.argv[3]); feasf = sys.argv[4]
rng = random.Random(seed)
q, N, lines, lof, coords = load_all(fn)
Mt = Matcher(q, N, lines, lof)
orbs = []; seen = set()
for ln in open(feasf):
    fl = [tuple(map(int, t.split(':'))) for t in ln.split()]
    key = tuple(sorted(fl))
    if fl and key not in seen: seen.add(key); orbs.append(fl)
print('feasible orbits', len(orbs), flush=True)
def pairs_info(flags):
    col = 0; conc = 0
    for i in range(len(flags)):
        for j in range(i + 1, len(flags)):
            p, l = flags[i]; p2, l2 = flags[j]
            if (Mt.Pm[p] >> p2) & 1: col += 1
            if (Mt.Lm[l] >> l2) & 1: conc += 1
    return col, conc
out = open(f'pairs_{seed}.txt', 'a')
t0 = time.time(); found = 0
for s in range(nseed):
    a = rng.randrange(len(orbs)); O1 = orbs[a]
    P1 = {p for p, _ in O1}; L1 = {l for _, l in O1}
    cnt = 0
    for b in range(len(orbs)):
        if b == a: continue
        O2 = orbs[b]
        if {p for p, _ in O2} & P1 or {l for _, l in O2} & L1: continue
        sz, _ = Mt.size(O1 + O2)
        if sz == N:
            cnt += 1; found += 1
            U = O1 + O2
            line = ' '.join(f'{p}:{l}' for p, l in U)
            out.write(line + '\n'); out.flush()
            if cnt <= 3: print('  union', 'col/conc', pairs_info(U), line, flush=True)
    print('O1', a, 'feasible partners', cnt, 'time %.1f' % (time.time() - t0), flush=True)
print('TOTAL unions', found, flush=True)
