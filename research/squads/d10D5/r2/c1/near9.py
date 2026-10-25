#!/usr/bin/env python3
"""near9.py GQBIN SOL0 "p:l ..." OUTPREFIX: among all flags f=(p,l) disjoint from the given k-set, pick the one whose
set+f has the LARGEST exact-coverage matching (sym.Matcher). Completes that matching to a bijection sigma (unmatched
points get unmatched lines) and writes lift2 OUTPREFIX.sol (nu from SOL0) and OUTPREFIX.sol.free (all freed points).
usage: python3 -I near9.py gq/gq_q7.bin ../../../../d10D7/graphs/d10D5_n4800_gqdm_q7.sol "266:64 ... 253:247" k9"""
import sys, time
sys.path.insert(0, '.')
from sym import *
fn = sys.argv[1]; sol0 = sys.argv[2]; F0 = [tuple(map(int, t.split(':'))) for t in sys.argv[3].split()]; outp = sys.argv[4]
q, N, lines, lof, coords = load_all(fn)
Mt = Matcher(q, N, lines, lof)
P0 = {p for p, _ in F0}; L0 = {l for _, l in F0}
best = (-1, None, None); t0 = time.time(); hist = {}
for p in range(N):
    if p in P0: continue
    for l in lof[p]:
        if l in L0: continue
        sz, ml = Mt.size(F0 + [(p, l)])
        hist[sz] = hist.get(sz, 0) + 1
        if sz > best[0]: best = (sz, (p, l), ml)
print('matching size histogram (top):', sorted(hist.items(), reverse=True)[:5], 'time %.1f' % (time.time() - t0), flush=True)
sz, f, ml = best
F = F0 + [f]
print('best extension', f, 'matching', sz, 'of', N, flush=True)
# complete to a bijection
used = set(x for x in ml if x >= 0)
free_lines = [m for m in range(N) if m not in used]
it = iter(free_lines)
sig = [ml[x] if ml[x] >= 0 else next(it) for x in range(N)]
assert sorted(sig) == list(range(N))
tok = open(sol0).read().split(); nu = tok[7 + 4 * N:7 + 4 * N + N * (q + 1)]
with open(outp + '.sol', 'w') as f_:
    f_.write(f'{q} 2 6 7 0\ncyc 6\n'); s = ' '.join(map(str, sig)); f_.write(s + '\n' + s + '\n')
    f_.write(' '.join(['1'] * N) + '\n' + ' '.join(['4'] * N) + '\n' + ' '.join(nu) + '\n')
with open(outp + '.sol.free', 'w') as f_: f_.write(' '.join(str(p) for p, _ in F) + '\n')
print('FLAGS', ' '.join(f'{p}:{l}' for p, l in F))
print('FREE', ' '.join(str(p) for p, _ in F))
print('WROTE', outp + '.sol')
