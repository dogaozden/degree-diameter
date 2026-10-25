"""Summarise the c4 sweep: per job stage-1 / stage-2 cost, lowest cost per order, cost-0 lifts and their apsp checks.
usage: python3 summary.py   (reads jobs1.txt, runs1/, runs2/, verify.log in this folder)"""
import os, re

C = os.path.dirname(os.path.abspath(__file__))


def cost(path):
    try:
        m = re.search(r'best_cost=(\d+)', open(path).read())
    except FileNotFoundError:
        return None
    return int(m.group(1)) if m else None


rows = []
for line in open(os.path.join(C, 'jobs1.txt')):
    b, g, t = line.split()
    p = t.split('_')
    order = int(p[1]) * int(p[2]) if p[0] in ('meta', 'prod') else int(p[1])
    rows.append((order, p[0], t, cost(os.path.join(C, 'runs1', t + '.out')), cost(os.path.join(C, 'runs2', t + '.out'))))

print('%-6s %-5s %-18s %-8s %-8s' % ('order', 'kind', 'group', 'seed1', 'seed2'))
best_per_order = {}
for order, kind, t, c1, c2 in rows:
    f = lambda c: '-' if c is None else str(c)
    print('%-6d %-5s %-18s %-8s %-8s' % (order, kind, t, f(c1), f(c2)))
    cs = [c for c in (c1, c2) if c is not None]
    if cs:
        best_per_order[order] = min(min(cs), best_per_order.get(order, 10 ** 9))
print()
print('lowest cost per order (both stages): ' + ', '.join('%d:%d' % (o, best_per_order[o]) for o in sorted(best_per_order)))
done = sum(1 for r in rows if r[3] is not None)
print('jobs with stage-1 result: %d of %d' % (done, len(rows)))
zero = [r for r in rows if r[3] == 0 or r[4] == 0]
print('cost-0 jobs: ' + (', '.join(r[2] for r in zero) if zero else 'none'))
vl = os.path.join(C, 'verify.log')
print('verify.log:')
print(open(vl).read() if os.path.exists(vl) else '  (none)')
