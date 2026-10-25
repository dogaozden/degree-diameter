"""newflags.py SOLFILE DROP(comma list) K SEED: keep the freed flags of SOLFILE minus DROP, add K new flags
(x, l), x on l, pairwise opposite to all other freed flags (x non-collinear, l disjoint) and to each other.
Prints FREE=... and FORCE=... for dmhub."""
import sys, random
sys.path.insert(0, '.')
from gq import load, perp, lperp
q, N, lines, lof = load('gq/gq_q7.bin')
rows = {}
for ln in open(sys.argv[1]):
    t = ln.split()
    if t and t[0] not in rows: rows[t[0]] = t[1:]
free = list(map(int, rows['free'])); sig = list(map(int, rows['sigma']))
drop = set(map(int, sys.argv[2].split(','))) if sys.argv[2] != '-' else set()
K = int(sys.argv[3]); rng = random.Random(int(sys.argv[4]))
keep = [p for p in free if p not in drop]
PER = {p: perp(lines, lof, p) for p in range(N)}
LPER = {l: lperp(lines, lof, l) for l in range(N)}
Lk = [sig[p] for p in keep]
cand = []
for x in range(N):
    if any(x in PER[p] for p in keep): continue           # x collinear with (or equal to) a kept freed point
    for l in lof[x]:                                       # lines through x
        if any(l in LPER[m] for m in Lk): continue       # l concurrent with a kept freed line
        cand.append((x, l))
print('kept', keep, 'kept lines', Lk, 'candidates', len(cand), file=sys.stderr)
best = None
for attempt in range(20000):
    chosen = []
    for x, l in rng.sample(cand, len(cand)):
        if all(x not in PER[xo] and l not in LPER[lo_] for xo, lo_ in chosen) and x != l:
            chosen.append((x, l))
            if len(chosen) == K: break
    if len(chosen) == K: best = chosen; break
if best is None: print('no set of', K, file=sys.stderr); sys.exit(1)
newfree = keep + [x for x, l in best]
print('FREE="' + ' '.join(map(str, newfree)) + '"')
print('FORCE="' + ' '.join(f'{x}:{l}' for x, l in best) + '"')
print('NEW', best, file=sys.stderr)
print('OLD-SIG-OF-NEW', [sig[x] for x, l in best], file=sys.stderr)
print('CHECK', len(newfree), len(set(newfree)), file=sys.stderr)
