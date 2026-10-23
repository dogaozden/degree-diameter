"""Markdown table of the best VALID orbit-search result per cell, from runs/*.log (orbq logs: RESULT + VALID lines).
usage: python3 records_table.py  (run from research/structured/tools or anywhere)"""
import glob, os, re, math
here = os.path.dirname(os.path.abspath(__file__))
runs = os.path.join(here, '..', 'runs')
def W(d, D):
    if D % 2: k = (D - 1) // 2; return 1 + sum(d * (d - 1) ** (2 * i - 1) for i in range(1, k + 1))
    k = D // 2; return d * sum((d - 1) ** (2 * i) for i in range(k))
# table values (DS14v2, TABLE.md) and our best before this job (research/frontier/sols at the start of the job)
TABLE = {(7,8): 80940, (8,8): 201480, (8,7): 40586, (7,9): 400160, (9,8): 449480, (8,9): 1091232, (7,10): 1987380,
         (8,10): 6927210, (10,9): 7057400, (13,8): 5314680, (11,9): 15200448, (10,10): 50331156, (13,9): 50990610,
         (14,9): 95087738, (16,9): 288939118, (13,10): 617330936}
PREV = {(7,8): 88920, (8,8): 225792, (8,7): 41040, (7,9): 416640, (9,8): 497904, (8,9): 1245312, (7,10): 2147040,
        (8,10): 7349616, (10,9): 7488000, (13,8): 6408480, (11,9): 16369920, (10,10): 57868272, (13,9): 62156160,
        (14,9): 111482880, (16,9): 316679760, (13,10): 636550992}
best = {}
valid, results = {}, {}
for f in glob.glob(os.path.join(runs, '*.log')) + glob.glob(os.path.join(runs, '*.rebuild.txt')) + glob.glob(os.path.join(runs, '*.lowmem.txt')):
    txt = open(f).read()
    for v in re.finditer(r'^VALID d=(\d+) D=(\d+) group=(.+?) N=(\d+) vertices=(\d+)', txt, re.M):
        valid.setdefault((int(v.group(1)), int(v.group(2)), int(v.group(4)), v.group(3)), os.path.basename(f).split('.')[0])
    for m in re.finditer(r'RESULT d=(\d+) D=(\d+) group=(.+?) N=(\d+) best=0 evals=(\d+) .*orbit k=(\d+) m=(\d+) f=(\d+)', txt):
        d, D, grp, N, ev, k, mm, ff = m.groups()
        results.setdefault((int(d), int(D), int(N), grp), (grp, int(ev), int(k), int(mm), int(ff)))
for key, (grp, ev, k, mm, ff) in results.items():
    if key not in valid: continue
    d, D, N, _ = key
    tag = valid[key]
    if not os.path.exists(os.path.join(here, '..', '..', 'frontier', 'sols', tag + '.txt')):
        cands = [os.path.basename(p)[:-4] for p in glob.glob(os.path.join(here, '..', '..', 'frontier', 'sols', 'd%dD%d_*orb*.txt' % (d, D)))
                 if open(p).readline().split()[-1] == str(N) and open(p).readline().split()[2] == grp.split()[0]]
        tag = cands[0] if cands else tag
    g = grp.replace(' x Z_', ' × Z').replace(' poly x^3+x+1', '').replace(' poly x^2+1', '').replace(' poly x^3+2x+1', '')
    insols = os.path.exists(os.path.join(here, '..', '..', 'frontier', 'sols', tag + '.txt'))
    if (d, D) not in best or (N, insols) > (best[(d, D)][0], best[(d, D)][7]):
        best[(d, D)] = (N, g, ev, k, mm, ff, tag, insols)
print('| cell | table (DS14v2) | our previous best | new | group, structure (k, m, f) | μ at new order | evals | file (../frontier/sols/) |')
print('|---|---|---|---|---|---|---|---|')
for (d, D) in sorted(best, key=lambda c: (c[1], c[0])):
    N, grp, ev, k, mm, ff, tag, _ = best[(d, D)]
    mu = N * math.exp(-W(d, D) / N); prev = PREV.get((d, D)); t = TABLE.get((d, D))
    gain = '(+%.1f %%)' % (100.0 * (2 * N / prev - 1)) if prev else ''
    print('| (%d,%d) | %s | %s | **%s** %s | %s; %d, %d, %d | %.1f | %.2g | %s.txt |' % (d, D, format(t, ',') if t else '–', format(prev, ',') if prev else '–', format(2 * N, ','), gain, grp, k, mm, ff, mu, ev, tag))
