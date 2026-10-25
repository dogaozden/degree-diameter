#!/usr/bin/env python3
"""relaxsol.py GQBIN "p:l p:l ..." SOL0 OUTPREFIX: card c5 round 2 (relaxed coverage).  Maximum exact-coverage matching
for the freed flags (sym.Matcher, forced flags kept), unmatched points completed to a bijection arbitrarily, so a union
with deficiency > 0 can still start dmhub's coverage annealing (COVIT).  Writes OUTPREFIX.sol (lift2 format: sigma twice,
mv0 all 1, mv1 all 4, SOL0's nu) and OUTPREFIX.sol.free; prints the deficiency N - matching size."""
import sys
sys.path.insert(0, '.')
from sym import load_all, Matcher
q, N, lines, lof, coords = load_all(sys.argv[1])
flags = [tuple(map(int, t.split(':'))) for t in sys.argv[2].split()]
tok = open(sys.argv[3]).read().split()
nu = tok[7 + 4 * N:7 + 4 * N + N * (q + 1)]
Mt = Matcher(q, N, lines, lof)
size, matchL = Mt.size(flags)
used = {l for l in matchL if l >= 0}
rest = iter([l for l in range(N) if l not in used])
mt = list(matchL)
for u in range(N):
    if mt[u] < 0: mt[u] = next(rest)
assert sorted(mt) == list(range(N))
for p, l in flags: assert mt[p] == l
out = sys.argv[4]
with open(out + '.sol', 'w') as f:
    f.write(f'{q} 2 6 7 0\ncyc 6\n'); s = ' '.join(map(str, mt)); f.write(s + '\n' + s + '\n')
    f.write(' '.join(['1'] * N) + '\n' + ' '.join(['4'] * N) + '\n' + ' '.join(nu) + '\n')
with open(out + '.sol.free', 'w') as f: f.write(' '.join(str(p) for p, l in flags) + '\n')
print('flags', len(flags), 'matching', size, 'deficiency', N - size, 'WROTE', out + '.sol', out + '.sol.free')
