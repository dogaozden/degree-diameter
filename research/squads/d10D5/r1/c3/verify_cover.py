"""verify_cover.py GQBIN SOL PAIRS: independent check (no bitmasks) of the exact-coverage conditions of each freed pair
(p, l = sigma(p), g, g2): (1) sigma is a bijection and sigma(p) = l; (2) for every opposite point u of p (not collinear,
u != p) some NON-freed x collinear with p (x != p) has u on sigma(x) [route p-L-x-sigma(x)-u]; (3) dually for every
line N opposite l: some non-freed point Y collinear with g2 (Y not on l) has N through Y with sigma(Y) concurrent with
l [route l-P-sigma(Y)-Y-N]. Prints the failing counts (0 = exact coverage holds)."""
import sys
sys.path.insert(0, '.')
from gq import load, perp, lperp
q, N, lines, lof = load(sys.argv[1])
tok = open(sys.argv[2]).read().split(); sig = list(map(int, tok[7:7 + N]))
assert sorted(sig) == list(range(N)), 'sigma not a bijection'
pairs = [tuple(map(int, ln.split())) for ln in open(sys.argv[3]) if ln.strip()]
freedP = {p for p, l, g, g2 in pairs}; freedL = {l for p, l, g, g2 in pairs}
bad = 0
for p, l, g, g2 in pairs:
    assert sig[p] == l, ('sigma(p) != l', p, l)
    P = perp(lines, lof, p)            # collinear with p, incl p
    Lp = lperp(lines, lof, l)          # concurrent with l, incl l
    # (2) point side: opposite points u of p need a non-freed x ~ p (x != p) with u on sigma(x)
    covered = set()
    for x in P:
        if x == p or x in freedP: continue
        covered.update(lines[sig[x]])
    opp = set(range(N)) - P
    miss = len(opp - covered); bad += miss
    # (3) line side: opposite lines N of l need a non-freed Y collinear with g2, Y not on l, with sigma(Y) concurrent with l
    Yset = perp(lines, lof, g2) - set(lines[l])
    cov2 = set()
    for Y in Yset:
        if Y in freedP or sig[Y] not in Lp or sig[Y] == l: continue
        cov2.update(lof[Y])
    oppL = set(range(N)) - Lp
    miss2 = len(oppL - cov2); bad += miss2
    print('pair', p, l, 'flag' if p in lines[l] else 'nonflag', 'miss_point', miss, 'miss_line', miss2)
    # holes: freed line in G (point side), freed point in Y (line side)
print('TOTAL MISSES', bad, 'freed', len(pairs))
