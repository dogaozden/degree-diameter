"""facts.py: check the triad facts of W(7) used in the flag analysis (sampled)."""
import sys, random, collections
sys.path.insert(0, '.')
from gq import load, perp, lperp
q, N, lines, lof = load('gq/gq_q7.bin')
P = [perp(lines, lof, p) for p in range(N)]          # incl p
Lp = [lperp(lines, lof, l) for l in range(N)]        # incl l
rng = random.Random(1)
cen = collections.Counter(); tr = collections.Counter()
for _ in range(60000):
    a, b, c = rng.sample(range(N), 3)
    if b in P[a] or c in P[a] or c in P[b]: continue
    cen[len(P[a] & P[b] & P[c])] += 1
for _ in range(60000):
    a, b, c = rng.sample(range(N), 3)
    if (set(lines[a]) & set(lines[b])) or (set(lines[a]) & set(lines[c])) or (set(lines[b]) & set(lines[c])): continue
    tr[len(Lp[a] & Lp[b] & Lp[c])] += 1
print('point triads pairwise noncollinear: centre counts (incl. the 3 points? no: P includes self, so check)', dict(cen))
print('line triads pairwise disjoint: transversal counts (incl. lines themselves)', dict(tr))
# pairwise facts
pc = collections.Counter(); lc = collections.Counter()
for a in range(N):
    for b in range(N):
        if a < b:
            if b in P[a]: pc[('col', len(P[a] & P[b]))] += 1
            else: pc[('non', len(P[a] & P[b]))] += 1
for a in range(N):
    for b in range(a + 1, N):
        if set(lines[a]) & set(lines[b]): lc[('conc', len(Lp[a] & Lp[b]))] += 1
        else: lc[('disj', len(Lp[a] & Lp[b]))] += 1
print('point pairs (P incl self):', dict(pc))
print('line pairs (Lp incl self):', dict(lc))
