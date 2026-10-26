# c7 analysis: E18 = median over seeds of (evals if solved else 3*evals) * exp((18 - mu)/4.5), per variant x group.
import json, math, re, os, statistics, collections
HERE = '/home/user/degree-diameter/research/squads/d16D10-r1/c7'
W = 183063616.0
rows = [json.loads(l) for l in open(os.path.join(HERE, 'results.jsonl')) if l.strip()]
groups = collections.OrderedDict()
for r in rows:
    if r.get('evals') is None:
        continue
    out = open(os.path.join(HERE, 'logs', r['tag'] + '.out')).read()
    m = re.search(r'N=(\d+)', out)
    N = int(m.group(1))
    mu = N * math.exp(-W / N)
    env = r['env']
    label = env.get('ORBIT', '') + (' ORBW=%s' % env['ORBW'] if 'ORBW' in env else '') + (' AR=%s' % env['AR'] if 'AR' in env else '')
    key = (r['group'], label)
    solved = r['best'] == 0
    eff = r['evals'] if solved else 3 * r['evals']
    groups.setdefault(key, {'mu': mu, 'N': N, 'runs': []})['runs'].append((r['seed'], solved, r['evals'], eff, r['check'], r['wall']))
print('%-12s %-22s %-18s %8s %6s %s' % ('group', 'variant', 'N (mu)', 'med_eff', 'E18', 'per-seed (seed:solved:evals:check)'))
best = None
for (g, label), v in groups.items():
    effs = [x[3] for x in v['runs']]
    med = statistics.median(effs)
    e18 = med * math.exp((18 - v['mu']) / 4.5)
    per = ' '.join('%d:%s:%d:%s' % (s, 'S' if so else 'U', ev, ck) for s, so, ev, _, ck, _ in sorted(v['runs']))
    print('%-12s %-22s %-18s %8.0f %6.0f %s' % (g, label, '%d (%.2f)' % (v['N'], v['mu']), med, e18, per))
    if g.startswith('sl 53'):
        cand = (e18, label, all(x[1] for x in v['runs']), len(v['runs']))
        if best is None or cand[0] < best[0]: best = cand
print('best sl53 x Z91 variant by E18 (1-3 seeds each):', best)
