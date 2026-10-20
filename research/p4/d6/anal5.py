import collections, itertools
from bstruct import unital
q=5
S, lines, spt, sl, blocks = unital(q, 1)
v=S[0]
thru=[b for b in blocks if v in b]
idx={s:i for i,b in enumerate(thru) for s in b if s!=v}
circles=set(frozenset(idx[s] for s in c) for c in blocks if v not in c)
cover=collections.defaultdict(set)
for C in circles:
    for x,y in itertools.combinations(sorted(C),2): cover[(x,y)]|=C
n=len(thru)
def aline(x,y):
    a,b=min(x,y),max(x,y)
    return frozenset(z for z in range(n) if z not in cover[(a,b)] or z in (x,y))
alines=set(aline(x,y) for x,y in itertools.combinations(range(n),2))
Bset=set(int(t) for t in open('runs/B_q5_line0.txt').read().split())
Bl=frozenset(idx[s] for s in Bset if s!=v)
par=[l for l in alines if not (l & Bl)]
print('lines parallel to B:', len(par))
W={sd:set(int(t) for t in open(f'runs/W_q5_line0_sa{sd}.txt').read().split()) for sd in (11,13)}
for li,l in enumerate(par):
    for sd in (11,13):
        ws=[w for w in W[sd] if idx[sl(w)] in l]
        print(li, sd, len(ws), end=' | ')
    common=[w for w in W[11]&W[13] if idx[sl(w)] in l]
    print('common', len(common))
print('--- free point sets per class')
for li,l in enumerate(par):
    F={}
    for sd in (11,13):
        F[sd]=set(int(p) for w in W[sd] if idx[sl(w)] in l for p in lines[w] if int(p) not in spt)
    print(li, len(F[11]), len(F[13]), len(F[11]&F[13]))
