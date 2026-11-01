#!/usr/bin/env python3
"""update_table_b.py (job beyond-d11b): splice the rows of cells_b.txt into research/frontier/beyond/BEYOND_TABLE.md.
Only cells whose check log says VALID are written (kind gen: haarcheck_gen log beyond11/runs/<stem>.gen.txt; kind check:
build_haar2.py [+ apsp] log research/frontier/runs/cloudcheck/<stem>.check.txt). Cells already in the table are replaced in
place; new cells go right after the largest existing row of their D. A later line for the same cell overrides an earlier one."""
import math, os, re
HERE = os.path.dirname(os.path.abspath(__file__))
FR = os.path.join(HERE, '..')
TAB = os.path.join(FR, 'beyond', 'BEYOND_TABLE.md')
def moore(d, D): return 2 * sum((d - 1) ** i for i in range(D))
def W(d, D):
    if D % 2 == 0: return sum(d * (d - 1) ** (2 * i) for i in range(D // 2))
    return 1 + sum(d * (d - 1) ** (2 * i - 1) for i in range(1, (D - 1) // 2 + 1))
def n_at_mu(d, D, mu):
    w = W(d, D); lo, hi = 1.0, 1e17
    for _ in range(300):
        mid = math.sqrt(lo * hi)
        if mid * math.exp(-w / mid) < mu: lo = mid
        else: hi = mid
    return lo
rows = {}
for line in open(os.path.join(HERE, 'cells_b.txt')):
    if not line.strip() or line.startswith('#'): continue
    cell, stem, rest = [x.strip() for x in line.split('|', 2)]
    note, kind = [x.strip() for x in rest.rsplit('|', 1)]
    note = note.replace('x|', 'x\\|')   # a bare | would split the markdown table cell
    d, D = map(int, cell.split(','))
    if kind == 'gen':
        log, sol = os.path.join(HERE, 'runs', stem + '.gen.txt'), os.path.join(HERE, 'sols', stem + '.txt')
        ok = os.path.exists(log) and any(l.startswith('VALID') for l in open(log))
        chk = f'haarcheck_gen VALID (research/frontier/runs/cloudcheck/{stem}.gen.txt)'
    else:
        log, sol = os.path.join(FR, 'runs', 'cloudcheck', stem + '.check.txt'), os.path.join(FR, 'sols', stem + '.txt')
        txt = open(log).read() if os.path.exists(log) else ''
        ok = re.search(r'^VALID d=', txt, re.M) is not None and 'INVALID' not in txt
        ap = 'RESULT VALID' in txt
        chk = (f'build_haar2.py VALID' + (' and all-pairs apsp VALID' if ap else '') +
               f' (research/frontier/runs/cloudcheck/{stem}.check.txt)')
    if not ok:
        print('not yet VALID:', cell, stem); continue
    hdr = open(sol).readline().split()
    N = int(hdr[hdr.index('N') + 1]); v = 2 * N
    mu = N * math.exp(-W(d, D) / N)
    rows[(d, D)] = (f'| ({d},{D}) | **{v:,}** | {100 * v / moore(d, D):.2f} | {moore(d, D) - 6:,} | {note}; mu = {mu:.2f} | '
                    f'{chk} | Haar size law at mu = 5: 2N = {2 * n_at_mu(d, D, 5):.3g} |')
lines = open(TAB).read().split('\n')
def key(l):
    m = re.match(r'\| \((\d+),(\d+)\) \|', l)
    return (int(m.group(1)), int(m.group(2))) if m else None
out, done = [], set()
for i, l in enumerate(lines):
    k = key(l)
    out.append(rows[k] if k in rows else l)
    if k in rows: done.add(k)
    if k and k[1] in (11, 12):
        nxt = key(lines[i + 1]) if i + 1 < len(lines) else None
        if not nxt or nxt[1] != k[1]:
            for d in range(k[0] + 1, 40):
                if (d, k[1]) in rows and (d, k[1]) not in done: out.append(rows[(d, k[1])]); done.add((d, k[1]))
open(TAB, 'w').write('\n'.join(out))
print('rows written:', sorted(done)); print('missing:', sorted(set(rows) - done))
