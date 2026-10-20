"""Does the whisker exact cover (ansatz) split into small independent pieces? Components of the graph on
{points X of full S-lines} + {free points}, joined through candidate whiskers.

python3 whisk_components.py q   (needs whiskers_ansatz_q{q}.json; HYPER env as for whisk_ansatz.py)
"""
import json
import sys
from collections import Counter

sys.argv = [sys.argv[0], sys.argv[1], 'none', '1']
src = open('whisk_ansatz.py').read().split('def solve')[0]
exec(src)
d = json.load(open(f'whiskers_ansatz_q{q}.json'))
E = set(s for B in d['blocks_v'] for s in B) - {v}
full_pts = [p for s in S if s != v and s not in E for p in lines[s]]
parent = {}


def find(x):
    while parent.setdefault(x, x) != x:
        parent[x] = parent[parent[x]]
        x = parent[x]
    return x


def union(a, b):
    parent[find(a)] = find(b)


ncand = 0
for X in full_pts:
    for k in through[X]:
        if k not in Sset and dist[N + k] == 6:
            ncand += 1
            for p in lines[k]:
                if p != X:
                    union(('X', X), ('p', p))
comps = Counter(find(('X', X)) for X in full_pts)
compsp = Counter(find(('p', p)) for p in free)
print(f'q={q}: candidates {ncand}, components {len(set(comps) | set(compsp))}, '
      f'sizes (X-points, free points): {sorted(Counter((comps[c], compsp[c]) for c in set(comps) | set(compsp)).items())}')
