"""Is N/B(k, o) a better predictor of 'solves' than N itself?  Within each D, over the open groups (bound not
violated), the AUC = P(score of a random solving group < score of a random non-solving group); 1 = perfect, 0.5 = none.
Also over ALL scanned groups (excluded ones have N/B > 1).  Usage: python3 cycloauc.py runs/cyclobound_d3D*.txt"""
import sys
def auc(pos, neg):
    if not pos or not neg:
        return float('nan')
    s = 0.0
    for a in pos:
        for b in neg:
            s += 1.0 if a < b else 0.5 if a == b else 0.0
    return s / (len(pos) * len(neg))
for fn in sys.argv[1:]:
    rows = []
    for line in open(fn):
        f = line.split()
        if len(f) < 9:
            continue
        p, k, r, o, N = map(int, f[:5]); sol = int(f[6].split('=')[1]); B = int(f[7].split('=')[1])
        rows.append((N, N / B if B > 0 else 99.0, sol > 0, f[8] == 'open', p, k, o))
    for scope, rs in (('open', [x for x in rows if x[3]]), ('all', rows)):
        pos = [x for x in rs if x[2]]; neg = [x for x in rs if not x[2]]
        print(f'{fn.split("_")[-1][:-4]:5s} {scope:4s} groups={len(rs):4d} solving={len(pos):2d}  '
              f'AUC(N)={auc([x[0] for x in pos], [x[0] for x in neg]):.3f}  '
              f'AUC(N/B)={auc([x[1] for x in pos], [x[1] for x in neg]):.3f}  '
              f'AUC(p)={auc([x[4] for x in pos], [x[4] for x in neg]):.3f}')
