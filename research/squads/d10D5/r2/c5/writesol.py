#!/usr/bin/env python3
"""writesol.py GQBIN "p:l p:l ..." SOL0 OUTPREFIX: perfect exact-coverage matching for the given freed flags, warm-started
from SOL0's sigma (as flaggreedy.py does), independent re-check with flagmatch.setup/hk, then writes OUTPREFIX.sol (lift2
format: sigma twice, mv0 all 1, mv1 all 4, SOL0's nu) and OUTPREFIX.sol.free."""
import sys
sys.path.insert(0, '.')
from gq import load, perp, lperp
import flagmatch
q, N, lines, lof = load(sys.argv[1])
flags = [tuple(map(int, t.split(':'))) for t in sys.argv[2].split()]
tok = open(sys.argv[3]).read().split(); sig0 = list(map(int, tok[7:7 + N])); nu = tok[7 + 4 * N:7 + 4 * N + N * (q + 1)]
# independent check (flagmatch.py rules, Hopcroft-Karp style augmenting paths)
adj = flagmatch.setup(q, N, lines, lof, flags)
size, _ = flagmatch.hk(adj, N, N)
print('flags', len(flags), 'independent matching size', size, 'of', N, flush=True)
# warm-started matching (same adjacency), starting from sigma0's allowed edges
F = {p: l for p, l in flags}; Fl = {l for p, l in flags}
matchR = [-1] * N; matchL = [-1] * N
for x in range(N):
    M = sig0[x]
    if M in adj[x] and matchR[M] < 0: matchR[M] = x; matchL[x] = M
for x, M in F.items():
    if matchR[M] >= 0 and matchR[M] != x: matchL[matchR[M]] = -1
    matchR[M] = x; matchL[x] = M
sys.setrecursionlimit(20000)
def aug(u, seen):
    for v in adj[u]:
        if v in seen: continue
        seen.add(v)
        if matchR[v] < 0 or aug(matchR[v], seen):
            matchR[v] = u; matchL[u] = v; return True
    return False
for u in range(N):
    if matchL[u] < 0: aug(u, set())
ok = sum(1 for u in range(N) if matchL[u] >= 0)
print('warm matching size', ok, 'changed from sigma0', sum(1 for x in range(N) if matchL[x] != sig0[x]), flush=True)
assert ok == N and len(set(matchL)) == N
for x in range(N):
    assert matchL[x] in adj[x] or x in F
    if x in F: assert matchL[x] == F[x]
out = sys.argv[4]
with open(out + '.sol', 'w') as f:
    f.write(f'{q} 2 6 7 0\ncyc 6\n'); s = ' '.join(map(str, matchL)); f.write(s + '\n' + s + '\n')
    f.write(' '.join(['1'] * N) + '\n' + ' '.join(['4'] * N) + '\n' + ' '.join(nu) + '\n')
with open(out + '.sol.free', 'w') as f: f.write(' '.join(str(p) for p, l in flags) + '\n')
print('FLAGS', ' '.join(f'{p}:{l}' for p, l in flags))
print('WROTE', out + '.sol', out + '.sol.free')
