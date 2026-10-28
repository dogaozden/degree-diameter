#!/usr/bin/env python3
"""Summarise results.jsonl: per (Delta, group, kind) mean and SD over the 8 seeds of mean_excess, and the per-q SD
of excess (for each q, SD over the 8 seeds of excess(q); reported as the mean over q of those SDs)."""
import json, statistics as st, collections
CD = '/home/user/degree-diameter/research/squads/thmfam-r1/c13'
recs = [json.loads(l) for l in open(f'{CD}/results.jsonl')]
cells = collections.defaultdict(list)
for r in recs:
    if r.get('error') or r.get('mean_excess') is None: continue
    cells[(r['Delta'], r['group'], r['kind'])].append(r)
lines = ['Delta group kind n_seeds mean_of_mean_excess sd_of_mean_excess mean_per_q_sd_excess min_mean max_mean']
for key in sorted(cells, key=lambda k: (k[1], k[2], k[0])):
    rs = cells[key]
    means = [r['mean_excess'] for r in rs]
    per_q = collections.defaultdict(list)
    for r in rs:
        for row in r['rows']:
            if 'excess' in row: per_q[row['q']].append(row['excess'])
    pq = [st.stdev(v) for q, v in per_q.items() if len(v) > 1]
    lines.append(f"{key[0]} {key[1]} {key[2]} {len(rs)} {st.mean(means):.3f} {st.stdev(means):.3f} {st.mean(pq):.3f} {min(means):.3f} {max(means):.3f}")
print('\n'.join(lines))
