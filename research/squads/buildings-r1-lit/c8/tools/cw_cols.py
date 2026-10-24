# Usage: python3 -I cw_cols.py tables.txt  -> prints (d, D=5, D=8) with colour and upper bound (nested table)
import sys, re
lines = open(sys.argv[1], encoding='utf-8').read().splitlines()
tabs, cur = [], None
for ln in lines:
    if ln.startswith('=== TABLE'):
        cur = []; tabs.append(cur); continue
    if cur is not None and ln.strip():
        cur.append(ln)
main, nested = tabs[0], tabs[2]
hdr = [c.strip() for c in main[0].split('||')][1:]
colour_name = {'#bbffff':'Bipartite Moore graph (optimal)','#0066CC':'Optimal (Bar-Yehuda&Etzion; Bond&Delorme)',
 '#993300':'Conder&Nedela; Delorme,Gomez,Quisquater; Loz','#ff0000':'Hafner; Loz (independent)',
 '#FF9900':'Loz, Perez-Roses, Pineda-Villavicencio joint project','#66ff66':'Delorme, Gomez, Quisquater',
 '#CC6600':'Delorme & Farhi graph duplications','yellow':'Feria-Puron, Miller, Pineda-Villavicencio; Araujo & Lopez',
 'pink':'Araujo & Lopez'}
def parse(row):
    return [c.strip() for c in row.split('||')]
mrows = {int(parse(r)[0]): parse(r)[1:] for r in main[1:]}
nrows = {int(parse(r)[0]): parse(r)[1:] for r in nested[1:]}
print('hdr k =', hdr)
for d in range(3, 17):
    out = []
    for kcol in ('5', '8'):
        j = hdr.index(kcol)
        cell = mrows[d][j]
        val = re.sub(r'\{.*', '', cell).strip().replace(' ', '')
        col = re.search(r'#[0-9A-Fa-f]{6}|yellow|pink', cell)
        ncell = nrows[d][j]
        ub = re.search(r'nested:([0-9 ]+?)\s*;\s*([0-9.]+%)', ncell)
        out.append(f"D={kcol}: best={val} colour={col.group(0) if col else '?'} [{colour_name.get(col.group(0) if col else '', '?')}] upper_bound={ub.group(1).replace(' ','') if ub else '?'} ratio={ub.group(2) if ub else '?'}")
    print(f"Delta={d} | " + ' | '.join(out))
