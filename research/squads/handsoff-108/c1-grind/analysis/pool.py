# pool CHAIN lines from unique grind logs (dedup by md5); writes chains_pool.tsv
import glob, hashlib, re, os, collections
seen = {}
rows = []
for f in sorted(glob.glob('raw/*.log')):
    data = open(f, 'rb').read()
    h = hashlib.md5(data).hexdigest()
    base = os.path.basename(f).split('__', 1)[1]
    if h in seen:
        continue
    seen[h] = base
    txt = data.decode('utf-8', 'replace').splitlines()
    grp = ''
    for line in txt:
        if line.startswith('group '):
            grp = line.split(',')[0][6:]
            grp = grp.replace('poly x^3+x+1 ', '')
            break
    for line in txt:
        m = re.match(r'CHAIN (\d+) min (\d+) secs (\d+) evals (\d+) S (.*)', line)
        if m:
            rows.append((grp, base.replace('.log', ''), int(m.group(1)), int(m.group(2)), int(m.group(3)), int(m.group(4))))
with open('chains_pool.tsv', 'w') as o:
    o.write('group\tfile\tchain\tmin\tsecs\tevals\n')
    for r in rows:
        o.write('\t'.join(map(str, r)) + '\n')
print('unique logs', len(seen), 'chains', len(rows))
bygrp = collections.defaultdict(list)
for r in rows:
    bygrp[r[0]].append(r)
for g, rs in bygrp.items():
    mins = sorted(r[3] for r in rs)
    secs = sum(r[4] for r in rs)
    n = len(mins)
    frac = lambda t: sum(1 for x in mins if x <= t)
    print(f'{g}: n={n} cpu_h={secs/3600:.2f} median={mins[n//2]} min={mins[0]} '
          + ' '.join(f'<={t}:{frac(t)}' for t in (3,6,9,12,15,18)))
