import sys
from collections import defaultdict, Counter
n = 27
V = list(map(int, sys.argv[1].split(',')))
toks = open('base_k33m.txt').read().split(); k = int(toks[0])
EA = [int(toks[1 + 2 * i]) for i in range(4 * k)]; EB = [int(toks[2 + 2 * i]) for i in range(4 * k)]; ne = 4 * k
# A side: source (a_i, 0). walk e1 e2 e3 e4: value = -v4 + v3 - v2 + v1 (cyclic, additive)
res = Counter(); crit = Counter(); tot = 0
for side in 'AB':
    for i in range(k):
        cov = defaultdict(set); d2 = set()
        for e1 in range(ne):
            if (EA if side == 'A' else EB)[e1] != i: continue
            for e2 in range(ne):
                if e2 == e1: continue
                if side == 'A' and EB[e2] != EB[e1]: continue
                if side == 'B' and EA[e2] != EA[e1]: continue
                end2 = EA[e2] if side == 'A' else EB[e2]
                x2 = (V[e1] - V[e2]) % n if side == 'A' else (V[e2] - V[e1]) % n
                d2.add((end2, x2))
                for e3 in range(ne):
                    if e3 == e2: continue
                    if side == 'A' and EA[e3] != EA[e2]: continue
                    if side == 'B' and EB[e3] != EB[e2]: continue
                    for e4 in range(ne):
                        if e4 == e3: continue
                        if side == 'A' and EB[e4] != EB[e3]: continue
                        if side == 'B' and EA[e4] != EA[e3]: continue
                        end = EA[e4] if side == 'A' else EB[e4]
                        x = (V[e1] - V[e2] + V[e3] - V[e4]) % n if side == 'A' else (-V[e1] + V[e2] - V[e3] + V[e4]) % n
                        cov[(end, x)].add((e1, e2, e3, e4))
        for j in range(k):
            for x in range(n):
                if (j, x) == (i, 0) or ((j, x) in d2 and (j, x) != (i, 0)): continue
                c = len(cov[(j, x)]); res[c] += 1; tot += 1
                if c == 1: crit[(side, next(iter(cov[(j, x)])))] += 1
print('pairs needing a 4-walk:', tot, 'multiplicity histogram:', sorted(res.items()))
print('critical walks (only walk to some pair):', len(crit))
