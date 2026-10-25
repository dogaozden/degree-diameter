"""c2 helper: summarize the lscreen TSVs for b33_1 and b33_2 (coverage per order, lowest costs)."""
import glob, os, sys
D = '/home/user/degree-diameter/research/squads/r2-smallfam/c2'
rows = []
for base in ['b33_1', 'b33_2']:
    p = os.path.join(D, f'lscreen_{base}_D10.tsv')
    if not os.path.exists(p):
        print(base, 'no tsv'); continue
    seen = {}
    for line in open(p):
        f = line.rstrip('\n').split('\t')
        if len(f) < 5:
            continue
        n, i, struct, ab, cost = f[0], f[1], f[2], f[3], f[4]
        if not i.isdigit():
            continue
        key = (int(n), int(i))
        seen[key] = (struct, ab, cost, f[5] if len(f) > 5 else '-')
    per = {}
    for (n, i), (struct, ab, cost, volts) in seen.items():
        per.setdefault(n, [0, 0])
        per[n][0] += 1
        if cost.replace(',', '').isdigit() or ',' in cost:
            per[n][1] += 1
            cmin = min(int(c) for c in cost.split(','))
            rows.append((cmin, base, n, i, struct, volts))
    print(base, 'coverage (groups evaluated per order):', ' '.join(f'{n}:{v[1]}' for n, v in sorted(per.items())))
rows.sort()
print('lowest costs (cost, base, order, id, structure, voltages):')
for r in rows[:12]:
    print(r)
