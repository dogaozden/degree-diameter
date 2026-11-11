# ORBW=3 subset of the pooled CHAIN lines (unique logs); prints per-group stats and tail counts
import glob, hashlib, re, os, collections, math
seen = {}; rows = []
for f in sorted(glob.glob('raw/*.log')):
    data = open(f, 'rb').read(); h = hashlib.md5(data).hexdigest()
    if h in seen: continue
    base = os.path.basename(f).split('__', 1)[1].replace('.log', '')
    seen[h] = base
    txt = data.decode('utf-8', 'replace').splitlines()
    if not any(l.startswith('ORBW=3: an uncovered') for l in txt): continue
    grp = [l for l in txt if l.startswith('group ')][0].split(',')[0][6:].replace('poly x^3+x+1 ', '')
    for line in txt:
        m = re.match(r'CHAIN (\d+) min (\d+) secs (\d+) evals (\d+)', line)
        if m: rows.append((grp, base, int(m.group(1)), int(m.group(2)), int(m.group(3)), int(m.group(4))))
print('ORBW3 unique logs', len([1 for h in seen]), 'chains', len(rows))
by = collections.defaultdict(list)
for r in rows: by[r[0]].append(r)
for g, rs in by.items():
    mins = sorted(r[3] for r in rs); n = len(mins); cpu = sum(r[4] for r in rs) / 3600
    files = len(set(r[1] for r in rs))
    print(f'{g}: files={files} n={n} cpu_h={cpu:.1f} median={mins[n//2]} mean={sum(mins)/n:.2f} min={mins[0]} '
          + ' '.join(f'<={t}:{sum(1 for x in mins if x<=t)}' for t in (3,6,9,12,15,18,21)))
    cnt = collections.Counter(mins)
    print('   hist:', ' '.join(f'{k}:{cnt[k]}' for k in range(0, 31) if cnt[k]))
    print('   per cpu-h <=9: %.3f  <=12: %.3f  <=15: %.3f' % (sum(1 for x in mins if x<=9)/cpu, sum(1 for x in mins if x<=12)/cpu, sum(1 for x in mins if x<=15)/cpu))
with open('chains_orbw3.tsv', 'w') as o:
    o.write('group\tfile\tchain\tmin\tsecs\tevals\n')
    for r in rows: o.write('\t'.join(map(str, r)) + '\n')
