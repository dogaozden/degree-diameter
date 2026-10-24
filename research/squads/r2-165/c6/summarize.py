#!/usr/bin/env python3
"""Summarise the chart-aware sweep (card C6).  Reads /tmp/claude-0/r2c6/out/*.txt (one ctrl_chart run each).
Writes results.tsv (one row per group and configuration) and prints the best cost per order.
Consistency check: a group's (best_cost, nbest, solutions) must be identical for all 8 relabelled pattern files of a
family and for every identity colour (bijection argument: relabelling colours permutes the ordered tuples)."""
import glob, os, re, collections
OUT = '/tmp/claude-0/r2c6/out'
rows = []
for fn in sorted(glob.glob(OUT + '/*.txt')):
    base = os.path.basename(fn)[:-4]
    name, cfg = base.split('__', 1)
    txt = open(fn).read().strip().splitlines()
    summ = [l for l in txt if l.startswith('m=')]
    if not summ:
        rows.append(dict(group=name, cfg=cfg, status='NO_RESULT', best=None)); continue
    s = summ[-1]
    get = lambda k: re.search(k + r'=(\S+)', s).group(1)
    sols = [l for l in txt if l.startswith('SOL')]
    rows.append(dict(group=name, cfg=cfg, status='ok', m=int(get('m')), best=int(get('best_cost')), nbest=int(get('nbest')),
                     solutions=int(get('solutions')), bestS=' '.join(s.split('bestS=')[1].split()),
                     sols=sols))
with open('/home/user/degree-diameter/research/squads/r2-165/c6/results.tsv', 'w') as f:
    f.write('group\tcfg\tm\tbest_cost\tnbest\tsolutions\tbestS\tstatus\n')
    for r in rows:
        f.write(f"{r['group']}\t{r['cfg']}\t{r.get('m','')}\t{r.get('best','')}\t{r.get('nbest','')}\t{r.get('solutions','')}\t"
                f"{r.get('bestS','')}\t{r['status']}\n")
done = [r for r in rows if r['status'] == 'ok']
print('runs finished', len(done), 'of', len(rows))
# consistency: per group and family
bad = 0
groups = collections.defaultdict(list)
for r in done: groups[r['group']].append(r)
for g, rs in groups.items():
    for fam in ('c4', 'c5'):
        fam_rs = [r for r in rs if r['cfg'].startswith(fam)]
        v = set((r['best'], r['nbest'], r['solutions']) for r in fam_rs)
        if len(v) > 1: bad += 1; print('INCONSISTENT', g, fam, v)
print('consistency violations', bad)
by_m = collections.defaultdict(list)
for r in done: by_m[r['m']].append(r)
for m in sorted(by_m):
    rs = by_m[m]
    bestv = min(r['best'] for r in rs)
    top = sorted([r for r in rs if r['best'] == bestv], key=lambda r: r['group'])
    perfect = [r for r in rs if r['solutions'] > 0]
    print(f"m={m}: best cost {bestv} in {len(top)} run(s), e.g. {top[0]['group']} [{top[0]['cfg']}] bestS={top[0]['bestS']}; perfect runs: {len(perfect)}")
