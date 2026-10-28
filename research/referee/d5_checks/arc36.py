"""Report §12 remark on the D->D arc 3->6 of the (13,5) record: free one more element x on that arc (delete its
matching edge, no hub on the new slots) and count bad pairs (a) in the two levels 3, 6 alone and (b) in the whole graph.
Usage: python3 arc36.py SOLUTION.json RECORD.edges OUT.edges seed"""
import json, sys, random
from test_theorems import two_level_bad
from gq import GQ
sol = json.load(open(sys.argv[1])); rng = random.Random(int(sys.argv[4]))
N = len(sol['W_points'])
G = GQ([sorted(l) for l in sol['W_lines']], N).dual()     # Q(4,q): point i = W-line i, line j = W-point j
nf = sol['nonfriendly']['3,6']; M, R = nf['M'], list(nf['R'])
x = rng.choice([a for a in range(N) if a not in R])
bad2 = two_level_bad(G, 'D', 'D', M, R + [x])
u = 3 * 2 * N + N + x; v = 6 * 2 * N + M[x]               # (x,3) is a line of a D level, M(x) a point of level 6
lines = open(sys.argv[2]).read().split('\n')
out = [lines[0]] + [l for l in lines[1:] if l.strip() and tuple(sorted(map(int, l.split()))) != tuple(sorted((u, v)))]
assert len(out) == len([l for l in lines if l.strip()]) - 1
open(sys.argv[3], 'w').write('\n'.join(out) + '\n')
print("extra freed element on arc 3->6: two-level bad (ordered level-3/level-6) pairs: %d" % len(bad2))
