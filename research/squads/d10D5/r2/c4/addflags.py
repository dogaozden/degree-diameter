"""addflags.py BASEFREE BASESOL M SEED: extend a flag set by M new flags, each free (collinear points, concurrent lines)
with some existing flag (new point p' collinear with a flag point p, not on its line l; new line = line(proj_l(p'), p')).
Prints FREE and FORCE strings and the free-pair count."""
import sys, random
sys.path.insert(0, '.')
from model import q, N, lines, lof, collinear, concurrent
bfree = list(map(int, open(sys.argv[1]).read().split()))
rows = [ln.split() for ln in open(sys.argv[2]) if ln.strip()]
sig = list(map(int, [r for r in rows if r[0] not in ('7', 'cyc') and len(r) == N][0]))
M = int(sys.argv[3]); rng = random.Random(int(sys.argv[4]))
flags = [(p, sig[p]) for p in bfree]
used_p = set(bfree); used_l = {l for _, l in flags}
def proj(p2, l):
    for y in lines[l]:
        if y != p2 and collinear(y, p2): return y
    return None
tries = 0
while len(flags) < len(bfree) + M and tries < 200000:
    tries += 1
    p, l = rng.choice(flags)
    cands = [x for L in lof[p] for x in lines[L] if x != p and x not in lines[l] and x not in used_p]
    if not cands: continue
    p2 = rng.choice(cands); y = proj(p2, l)
    if y is None: continue
    l2 = next(L for L in lof[p2] if y in lines[L]) if any(y in lines[L] for L in lof[p2]) else None
    if l2 is None or l2 in used_l or l2 == l: continue
    flags.append((p2, l2)); used_p.add(p2); used_l.add(l2)
fr = sum(1 for i in range(len(flags)) for j in range(i) if collinear(flags[i][0], flags[j][0]) and concurrent(flags[i][1], flags[j][1]))
print('k', len(flags), 'free pairs', fr, file=sys.stderr)
open(sys.argv[5] + '.free', 'w').write(' '.join(str(p) for p, _ in flags) + '\n')
open(sys.argv[5] + '.force', 'w').write(' '.join(f'{p}:{l}' for p, l in flags) + '\n')
print(' '.join(str(p) for p, _ in flags))
