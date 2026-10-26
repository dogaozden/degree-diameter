"""Relaxed sets for build_relaxed.py.  usage: python3 mk_relaxed.py q in_T.txt(relaxed.c output) outT.json [avoidT.json]
With avoidT, points on the spread lines through the partnered points of avoidT may not be partnered (writes the input
file for relaxed.c instead and exits).  Without, converts relaxed.c output to json after checking."""
import sys, json, numpy as np
from gqlib import W, regular_spread_W
q = int(sys.argv[1]); G = W(q); S = regular_spread_W(G); Sset = set(S)
lid = {}
for li, l in enumerate(G.lines):
    for a in l:
        for b in l:
            if a != b: lid[(a, b)] = li
def check(T):
    for x in T:
        nb = [y for y in T if y != x and G.col[x, y]]
        assert len(nb) <= 1 and all(lid[(x, y)] not in Sset for y in nb)
    return sum(1 for x in T for y in T if x < y and G.col[x, y])
if len(sys.argv) > 4:
    A = json.load(open(sys.argv[4])); P = [x for x in A if any(G.col[x, y] for y in A if y != x)]
    X = {next(l for l in G.plines[m] if l in Sset) for m in P}
    bad = {p for l in X for p in G.lines[l]}
    with open(sys.argv[2], 'w') as f:
        f.write('%d\n' % G.np)
        for i in range(G.np):
            nbs = np.nonzero(G.col[i])[0]
            f.write('%d ' % len(nbs) + ' '.join('%d %d' % (j, 1 if (lid[(i, j)] in Sset or i in bad or j in bad) else 0) for j in nbs) + '\n')
    print('wrote input avoiding', len(X), 'spread lines')
else:
    T = [int(x) for x in open(sys.argv[2]).read().split()[1:]]
    pairs = check(T); json.dump(sorted(T), open(sys.argv[3], 'w')); print('relaxed set', len(T), 'pairs', pairs)
