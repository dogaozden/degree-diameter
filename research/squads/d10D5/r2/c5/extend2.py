#!/usr/bin/env python3
"""extend.py GQBIN BASESOL BASEFREE OUT.txt: card c5 round 2, k = 9 = c5's valid single order-8 orbit (8 flags) plus ONE
extra flag (p, l), p and l new.  BASESOL line 3 = sigma of the k=8 solution, BASEFREE = its freed points.  Tests every
genuine flag (p, l) (p not freed, l not a freed line) for exact coverage matching == N; writes the feasible 9-flag sets
to OUT.txt as  size cp cl flags  (cp / cl = collinear freed-point pairs / concurrent freed-line pairs), best first."""
import sys
sys.path.insert(0, '.')
from sym import load_all, Matcher
q, N, lines, lof, coords = load_all('gq/gq_q7.bin')
tok = open(sys.argv[2]).read().split()
sig = list(map(int, tok[7:7 + N]))
freed = list(map(int, open(sys.argv[3]).read().split()))
base = [(p, sig[p]) for p in freed]
Mt = Matcher(q, N, lines, lof)
FP = {p for p, _ in base}; FL = {l for _, l in base}
print('base flags', len(base), 'matching', Mt.size(base)[0], flush=True)


def ucount(U):
    cp = sum(1 for i in range(len(U)) for j in range(i) if Mt.Pm[U[i][0]] >> U[j][0] & 1)
    cl = sum(1 for i in range(len(U)) for j in range(i) if Mt.Lm[U[i][1]] >> U[j][1] & 1)
    return cp, cl


res = []; tested = 0
for l in range(len(lines)):
    if l in FL: continue
    for p in lines[l]:
        if p in FP: continue
        tested += 1
        U = base + [(p, l)]
        sz = Mt.size(U)[0]
        if sz >= N - 4:
            cp, cl = ucount(U)
            res.append((sz, cp, cl, U))
res.sort(key=lambda t: (-t[0], -(t[1] + t[2])))
with open(sys.argv[4], 'w') as f:
    for sz, cp, cl, U in res:
        f.write(f'{sz} {cp} {cl} ' + ' '.join(f'{p}:{l}' for p, l in U) + '\n')
print('tested', tested, 'sets with deficiency <= 4:', len(res), flush=True)
from collections import Counter
print('size counts', sorted(Counter(sz for sz, _, _, _ in res).items(), reverse=True), flush=True)
for sz, cp, cl, U in res[:5]: print('TOP size', sz, 'cp', cp, 'cl', cl, 'flags', ' '.join(f'{p}:{l}' for p, l in U), flush=True)
