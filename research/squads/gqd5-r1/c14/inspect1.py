import sys, subprocess
from collections import defaultdict, deque
sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r1/c14')
from surg import base, match, key
e_idx = int(sys.argv[1])
dset = {match[e_idx]}
edges = [e for e in base if key(*e) not in dset]
adj = defaultdict(set)
for a, b in edges: adj[a].add(b); adj[b].add(a)
print('deleted', match[e_idx], 'point end', match[e_idx][0] // 6, 'h', match[e_idx][0] % 6)
bad = []
for s in range(1020):
    d = {s: 0}; fr = [s]
    for k in range(5):
        nf = []
        for x in fr:
            for y in adj[x]:
                if y not in d: d[y] = k + 1; nf.append(y)
        fr = nf
    for t in range(s + 1, 1020):
        if t not in d: bad.append((s, t))
print(len(bad))
def name(v):
    return ('P' if v < 510 else 'L') + str(v // 6 if v < 510 else (v - 510) // 6) + '.' + str(v % 6)
inv = set()
for s, t in bad[:40]: print(name(s), name(t), end='; ')
print()
ends = set([match[e_idx][0], match[e_idx][1]])
print('bad pairs touching deleted endpoints', sum(1 for s, t in bad if s in ends or t in ends), 'of', len(bad))
