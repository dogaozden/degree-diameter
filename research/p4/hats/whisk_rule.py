"""Look for a local rule behind the exact whisker sets: compare chosen and unchosen candidate whiskers by the
blocks B(p) of their free points (how they meet E = empty S-lines, and the q blocks through v).

python3 whisk_rule.py q   (HYPER env as for whisk_ansatz.py)
"""
import json
import sys
from collections import Counter

sys.argv = [sys.argv[0], sys.argv[1], 'none', '1']
src = open('whisk_ansatz.py').read().split('def solve')[0]
exec(src)
d = json.load(open(f'whiskers_ansatz_q{q}.json'))
W = set(d['whiskers'])
Bv = [set(B) - {v} for B in d['blocks_v']]
E = set().union(*Bv)
allBv = [set(B) - {v} for B in thru_v]


def Bof(p):
    return frozenset(Sline_of[[x for x in lines[k] if x in Sline_of][0]] for k in through[p])


def sig(k, X):
    # for each free point p on candidate line k: (|B(p) & E|, number of chosen blocks through v that B(p) meets,
    # pattern of how B(p) meets all q^2 blocks through v)
    out = []
    for p in lines[k]:
        if p == X:
            continue
        B = Bof(p)
        out.append((len(B & E), sum(1 for b in Bv if B & b)))
    return tuple(sorted(out))


stat = Counter()
full_pts = [p for s in S if s != v and s not in E for p in lines[s]]
for X in full_pts:
    for k in through[X]:
        if k in Sset or dist[N + k] != 6:
            continue
        stat[(k in W, sig(k, X))] += 1
for key, c in sorted(stat.items()):
    print(key, c)
