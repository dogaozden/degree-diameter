# Summarise the interleaved A/B run: arm R (random start) vs arm B (best of 50 by C3E).
import re, sys, numpy as np
rows = []
for line in open('ab.log', errors='replace'):
    m = re.match(r'CHAIN (\d+) min (\d+) arm (\w) startE (\d+) startstat ([\d.]+) secs (\d+) evals (\d+)', line)
    if m:
        k, mn, arm, se, ss, secs, ev = m.group(1), int(m.group(2)), m.group(3), int(m.group(4)), float(m.group(5)), int(m.group(6)), int(m.group(7))
        e_start = se; c3 = int(round((ss - se) / 1000.0))   # startstat = 1000*c3 + energy, energy may exceed 1000
        rows.append((int(k), arm, mn, se, c3, e_start, secs, ev))
print('chains logged:', len(rows))
def mw(a, b):
    # Mann-Whitney U p-value (normal approx, two-sided, ties averaged)
    from math import erf, sqrt
    x = np.concatenate([a, b]); r = np.empty(len(x)); o = x.argsort(); r[o] = np.arange(1, len(x) + 1)
    _, inv, cnt = np.unique(x, return_inverse=True, return_counts=True)
    avg = np.cumsum(cnt) - (cnt - 1) / 2.0; rk = avg[inv]
    U = rk[:len(a)].sum() - len(a) * (len(a) + 1) / 2
    mu = len(a) * len(b) / 2; sd = np.sqrt(len(a) * len(b) * (len(a) + len(b) + 1) / 12)
    z = (U - mu) / sd; p = 2 * (1 - 0.5 * (1 + erf(abs(z) / sqrt(2))))
    return U / (len(a) * len(b)), p
if rows:
    for arm in 'RB':
        sel = [r for r in rows if r[1] == arm]
        if not sel: continue
        mins = np.array([r[2] for r in sel]); se = np.array([r[3] for r in sel]); c3 = np.array([r[4] for r in sel])
        print('arm %s: n=%d  min: best %d median %.1f mean %.2f | <=9: %d  <=12: %d | start energy median %.0f | start c3=0 frac %.2f | evals/chain %.0f' % (
            arm, len(sel), mins.min(), np.median(mins), mins.mean(), (mins <= 9).sum(), (mins <= 12).sum(), np.median(se), (c3 == 0).mean(), np.mean([r[7] for r in sel])))
    R = np.array([r[2] for r in rows if r[1] == 'R']); B = np.array([r[2] for r in rows if r[1] == 'B'])
    if len(R) > 2 and len(B) > 2:
        auc, p = mw(B, R)   # P(min_B > min_R): < 0.5 means arm B reaches lower minima
        print('P(min_B > min_R) = %.3f (Mann-Whitney two-sided p = %.3f); lower = biased start better' % (auc, p))
    # within-arm: does the start (c3, start energy) predict the chain minimum?
    for arm in 'RB':
        sel = [r for r in rows if r[1] == arm]
        if len(sel) > 5:
            mins = np.array([r[2] for r in sel], float); se = np.array([r[3] for r in sel], float); c3 = np.array([r[4] for r in sel], float)
            rk = lambda v: v.argsort().argsort()
            print('arm %s: Spearman(chain min, start energy) = %.3f ; Spearman(chain min, start c3) = %.3f' % (
                arm, np.corrcoef(rk(mins), rk(se))[0, 1], np.corrcoef(rk(mins), rk(c3))[0, 1] if c3.std() > 0 else float('nan')))
