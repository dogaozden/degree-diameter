# B6 analysis: per-sample lines "B6 t cost kind tr ord code" from RANDORB runs; classes = order of x1 (kind 1) or z0 (kind 0).
import sys, statistics as st
from collections import defaultdict
W_CLASS = {2: 29403, 3: 59048, 11: 296460, 61: 1764180, 121: 3261060, 122: 1764180}   # PSL(2,243) element counts by order
Qn = sum(W_CLASS.values()) + 1
DEG = 10**6
def load(path):
    rows = []
    for line in open(path):
        p = line.split()
        if len(p) == 7 and p[0] == 'B6' and p[1].isdigit():
            t, cost, kind, tr, o, code = map(int, p[1:])
            rows.append(dict(t=t, cost=cost, kind=kind, tr=tr, ord=o, code=code, cls=('z0' if kind == 0 else 'ord%d' % o)))
    return rows
def summ(rows):
    c = [r['cost'] for r in rows]; nd = [r['cost'] for r in rows if r['cost'] <= DEG]
    deg = len(c) - len(nd)
    return dict(n=len(c), deg=deg, degfrac=deg / max(1, len(c)), mean_all=st.mean(c) if c else float('nan'),
                med_all=st.median(c) if c else float('nan'), min=min(c) if c else -1,
                mean_nd_over10=(st.mean(nd) / 10 if nd else float('nan')),
                sd_nd_over10=(st.pstdev(nd) / 10 if len(nd) > 1 else float('nan')),
                med_nd_over10=(st.median(nd) / 10 if nd else float('nan')), min_nd_over10=(min(nd) / 10 if nd else float('nan')))
def table(title, rows):
    by = defaultdict(list)
    for r in rows: by[r['cls']].append(r)
    print(f"## {title}  ({len(rows)} samples)")
    print("| class | n | degenerate (cost>1e6) | mean cost | median cost | mean cost/10 (non-degen.) | sd of mean | median cost/10 (non-degen.) | min cost/10 |")
    print("|---|---|---|---|---|---|---|---|---|")
    keys = sorted(by, key=lambda k: (k != 'z0', int(k[3:]) if k.startswith('ord') else 0))
    for k in keys:
        s = summ(by[k])
        print(f"| {k} | {s['n']} | {s['deg']} ({100*s['degfrac']:.0f}%) | {s['mean_all']:.4g} | {s['med_all']:.4g} | {s['mean_nd_over10']:.2f} | {s['sd_nd_over10']/max(1,s['n'])**0.5:.2f} | {s['med_nd_over10']:.2f} | {s['min_nd_over10']:.1f} |")
    s = summ(rows)
    print(f"| all | {s['n']} | {s['deg']} ({100*s['degfrac']:.0f}%) | {s['mean_all']:.4g} | {s['med_all']:.4g} | {s['mean_nd_over10']:.2f} | | {s['med_nd_over10']:.2f} | {s['min_nd_over10']:.1f} |")
    print()
    return by
if __name__ == '__main__':
    for path in sys.argv[1:]:
        rows = load(path)
        if not rows: print(path, 'no B6 lines'); continue
        by = table(path, rows)
        # trace-in-GF(3) split (tr <= 1 after sign normalisation), non-degenerate only
        a = [r['cost'] / 10 for r in rows if r['cost'] <= DEG and r['kind'] == 1 and r['tr'] <= 1]
        b = [r['cost'] / 10 for r in rows if r['cost'] <= DEG and r['kind'] == 1 and r['tr'] > 1]
        if a and b: print(f"trace in GF(3) (tr<=1): n={len(a)} mean {st.mean(a):.2f};  other z1 traces: n={len(b)} mean {st.mean(b):.2f}\n")
