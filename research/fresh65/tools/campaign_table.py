# Table of the exhaustive Haar campaign from hx2/*.log (job fresh-6-5)
import glob, re, os, sys
D = os.path.dirname(os.path.abspath(__file__)) + '/../hx2'
names = {}
txt = open(D + '/export.log').read()   # GAP wraps long Print lines, so match across newlines
for m in re.finditer(r'EXPORTED \S*/h(\d+)_(\d+)\.txt\s+n=\s*\d+\s+\|Aut\|=(\d+)\s+gens=\d+\s+([^\n]*)', txt):
    names[(int(m.group(1)), int(m.group(2)))] = (m.group(4).strip(), int(m.group(3)))
rows = []
for f in glob.glob(D + '/h*_*.log'):
    m = re.search(r'h(\d+)_(\d+)\.log$', f)
    n, i = int(m.group(1)), int(m.group(2))
    txt = open(f).read()
    d = re.search(r'DONE N=\d+ pairs=\S+ sets=(\d+) Acovered=(\d+) valid=(\d+) minA=(\d+)', txt)
    bmin = min([int(x) for x in re.findall(r'Bunc=(\d+)', txt)] or [None]) if 'Bunc' in txt else None
    rows.append((n, i, names.get((n, i), ('?', 0)), d.groups() if d else None, bmin))
rows.sort()
lo = int(sys.argv[1]) if len(sys.argv) > 1 else 0; hi = int(sys.argv[2]) if len(sys.argv) > 2 else 10**9
print('| order | id | group | Aut | sets checked | S covering side A | valid | min uncovered (A side) | min B miss when A covered |')
print('|---|---|---|---|---|---|---|---|---|')
for n, i, (nm, aut), d, bmin in rows:
    if not (lo <= n <= hi): continue
    if d: print(f'| {n} | {i} | {nm} | {aut} | {int(d[0]):,} | {d[1]} | {d[2]} | {d[3]} | {bmin if bmin is not None else ("≥ 4" if int(d[1]) else "–")} |')
    else: print(f'| {n} | {i} | {nm} | {aut} | running | | | | |')
