#!/usr/bin/env python3
"""Turn the output of speed_bench.sh into the markdown table at the top of SPEEDUP.md.
usage: speed_table.py BENCH_OUTPUT"""
import re, sys

def kv(s):
    return dict(re.findall(r'([\w/]+)=([^\s]+)', s))

cells, cur = [], None
for line in open(sys.argv[1]):
    line = line.rstrip('\n')
    if line.startswith('=== '):
        dD, grp = line[4:].split(' ', 2)[:2], line[4:].split(' ', 2)[2]
        g = grp.split()
        cur = {'cell': '(%s,%s)' % tuple(dD), 'grp': ' '.join(g[:-1]) + ' × Z' + g[-1]}
        cells.append(cur)
    elif cur is None:
        continue
    elif line.startswith('RANDSAMPLE'):
        cur['rs'] = 'yes' if 'identical' in line else 'NO'
    elif line.startswith('BENCH'):
        d = kv(line)
        cur['N'] = int(d['N'])
        cur['bench%s' % d['FAST']] = float(d['ms/eval'])
    elif line.startswith('E2E'):
        f = re.search(r'FAST=(\d)', line).group(1)
        d = kv(line.split('TRACE', 1)[1]) if 'TRACE' in line else {}
        cur['e2e%s' % f] = d
    elif line[:3] in ('H3 ', 'HF ') and 'RESULT' in line:
        d = kv(line)
        cur[line[:2]] = float(d['evals']) / float(d['time'])

def fx(a, b):
    return '%.2f' % (a / b) if a and b else '–'

print('| cell, group | N | same RANDSAMPLE costs | ms/eval FAST=0 → 2 | E2E steps | E2E s FAST=0 → 2 | E2E factor '
      '| same trajectory hash | haar_gen3 evals/s | haar_fast evals/s | factor |')
print('|---|---|---|---|---|---|---|---|---|---|---|')
for c in cells:
    e0, e2 = c.get('e2e0', {}), c.get('e2e2', {})
    t0, t2 = float(e0.get('time', 0)), float(e2.get('time', 0))
    same = 'yes' if e0.get('hash') and e0.get('hash') == e2.get('hash') else 'NO'
    b0, b2 = c.get('bench0'), c.get('bench2')
    print('| %s %s | %s | %s | %s → %s (%s×) | %s | %.1f → %.1f | **%s** | %s | %.0f | %.0f | %s |' % (
        c['cell'], c['grp'], format(c.get('N', 0), ','), c.get('rs', '–'),
        '%.3g' % b0 if b0 else '–', '%.3g' % b2 if b2 else '–', fx(b0, b2),
        e0.get('steps', '–'), t0, t2, fx(t0, t2), same, c.get('H3', 0), c.get('HF', 0), fx(c.get('HF'), c.get('H3'))))
