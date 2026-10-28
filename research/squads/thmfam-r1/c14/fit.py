#!/usr/bin/env python3
# Least-squares fit of excess = a + b*x, x = log_5 |G|, |G| = vertices//2 (scorer convention), over q in 23..199.
import json, math, glob, sys, statistics as st
T = '/home/user/degree-diameter/research/squads/thmfam-r1/c14'
def load(files):
    rows = {}
    for f in files:
        for r in json.load(open(f))['rows']:
            if 'excess' in r: rows[r['q']] = r
    return [rows[q] for q in sorted(rows)]
def fit(rows):
    xs = [math.log(r['vertices'] // 2, 5) for r in rows]
    ys = [r['excess'] for r in rows]
    n = len(xs); mx = sum(xs) / n; my = sum(ys) / n
    sxx = sum((x - mx) ** 2 for x in xs); sxy = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
    b = sxy / sxx; a = my - b * mx
    res = [y - (a + b * x) for x, y in zip(xs, ys)]
    rsd = math.sqrt(sum(e * e for e in res) / (n - 2))
    return dict(n_q=n, q_min=None, slope=round(b, 4), intercept=round(a, 4), resid_sd=round(rsd, 4),
                x_range=[round(min(xs), 3), round(max(xs), 3)])
out = {}
lps = load([f'{T}/lps_23_112.json', f'{T}/lps_113_199.json'])
out['LPS_p5_pgl'] = fit(lps); out['LPS_p5_pgl']['q_min'] = lps[0]['q']; out['LPS_p5_pgl']['q_max'] = lps[-1]['q']
seeds = []
for s in (1, 2, 3):
    fs = [f'{T}/rand_s{s}_23_112.json', f'{T}/rand_s{s}_113_199.json']
    try:
        rr = load(fs)
    except Exception as e:
        print('seed', s, 'missing', e); continue
    if len(rr) < 38: print('seed', s, 'incomplete rows', len(rr))
    seeds.append(fit(rr)); seeds[-1]['seed'] = s
    seeds[-1]['mean_excess'] = round(st.mean(r['excess'] for r in rr), 3)
out['random_psl_seeds'] = seeds
if seeds:
    out['random_mean_slope'] = round(st.mean(s['slope'] for s in seeds), 4)
    out['random_mean_intercept'] = round(st.mean(s['intercept'] for s in seeds), 4)
    out['random_mean_resid_sd'] = round(st.mean(s['resid_sd'] for s in seeds), 4)
    out['score_slope_LPS_minus_random'] = round(out['LPS_p5_pgl']['slope'] - out['random_mean_slope'], 4)
    out['LPS_mean_excess'] = round(st.mean(r['excess'] for r in lps), 3)
print(json.dumps(out, indent=1))
