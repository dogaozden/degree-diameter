import sys, glob, collections
rows = []
for fn in glob.glob('/tmp/claude-0/cal_out_*.txt') + glob.glob(sys.argv[1] if len(sys.argv) > 1 else '/nonexistent'):
    for l in open(fn):
        b, t, s, r = l.strip().split('|', 3)
        d = dict(x.split('=') for x in r.split() if '=' in x)
        if 'm' not in d: continue
        k = int(d['k']); rows.append((k, int(d['m']), int(d['best_cost']), b.split('/')[-1], t.split('/')[-1]))
print(len(rows), 'runs')
best = collections.defaultdict(lambda: (999, None))
for k, m, c, b, t in rows:
    if c < best[(k, m)][0]: best[(k, m)] = (c, b + ' ' + t)
nperfect = collections.Counter((k, m) for k, m, c, b, t in rows if c == 0)
for key in sorted(best):
    print('k=%d m=%d best_cost=%d (%s)  perfect runs: %d' % (key[0], key[1], best[key][0], best[key][1], nperfect[key]))
