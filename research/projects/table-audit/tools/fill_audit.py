"""Fill the generated parts of AUDIT.md (summary counts, Loz reproduction table) from cells.csv (table-audit)."""
import csv, os, re
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
rows = list(csv.DictReader(open(os.path.join(HERE, 'cells.csv'))))
cell = lambda r: f"({r['d']},{r['D']})"
yes = [r for r in rows if r['rebuilt'] == 'yes']
order = [r for r in rows if r['rebuilt'] == 'order']
bad = lambda r: r['flag'].startswith('does not check out') or r['flag'].startswith('INVALID as read')
d8 = [r for r in rows if bad(r)]
none = [r for r in rows if r['rebuilt'] == 'no' and not bad(r)]
loz_o = [r for r in order if r['holder'].startswith('Loz')]
loz_n = [r for r in none if r['holder'].startswith('Loz')]
pend = [r for r in rows if r['check'].startswith('PENDING')]
summary = f"""Of the 112 cells (counts from cells.csv{'; checks still running when this was written: ' + ', '.join(cell(r) for r in pend) if pend else ''}):

- **{len(yes)} rebuilt** with the holder's own construction, or from the holder's own graph file, at exactly the table value and
  checked valid: the 27 Moore cells, (3,5), (7,3), (3,7), (4,5), (4,7), the Delorme–Farhi cells at D = 4 and 6 (10),
  the three D = 3 AL/FMP cells, and (6,7), (8,7) (Delorme 1985 §9).
- **{len(order)} reproduced at exactly the table order** by a construction of the same family or a graph found here, when the
  holder's own description is missing: the 15 green D = 5 and D = 7 cells (polygon covers), (3,8) and (3,10) (cyclic
  lifts found by the squad and the lead), (16,3) (a Delorme–Farhi duplication on PG(2,13)), (13,8) (round 2: a Haar graph
  of PSL(2,37) × Z105; the DGQ construction itself is not known), and {len(loz_o)} Loz cells as Haar graphs of
  metacyclic groups (§3).
- **{len(d8)} INVALID as read**: {', '.join(cell(r) for r in d8)}. Their values are Gómez's ΩH_q (PhD thesis,
  Barcelona 1986, §2.9.3), but that construction, as drawn, has diameter 9, not 8 (§4; witness pair for (10,8) in
  checks/witness_omega7_thesis.txt). Relabelling the copies freely fixes it at q = 2 and 3 but no such labelling is known
  at the table's q = 7..13 (§7).
- **{len(none)} have no traceable construction**: {len(loz_n)} Loz cells (data lost: {', '.join(cell(r) for r in loz_n)}),
  and {', '.join(cell(r) for r in none if not r['holder'].startswith('Loz'))}."""
grp = lambda r: re.search(r'Haar graph of meta (\d+) (\d+) \d+', r['construction'])
lines = []
for r in sorted(loz_o, key=lambda r: (int(r['d']), int(r['D']))):
    g = grp(r)
    lines.append(f"| {cell(r)} | {int(r['value']):,} | Z{g.group(1)} ⋊ Z{g.group(2)} |")
half = (len(lines) + 1) // 2
L, R = lines[:half], lines[half:] + ['|  |  |  |'] * (half - len(lines[half:]))
table = '| cell | value | group | cell | value | group |\n|---|---:|---|---|---:|---|\n' + '\n'.join(l + r[1:] for l, r in zip(L, R))
loz = f"""{len(loz_o)} Loz cells are reached at exactly the table order (round 1: 23 of the 24 tried; round 2 went through
the rest in increasing size with the same tool, tools/exact_haar.py driving research/frontier/haar_gen3; above 10⁶
vertices each graph passes two independent two-BFS checkers, checks/haar_huge.txt):

{table}

These are graphs of the table's order, not necessarily Loz's graphs. (4,8) and (4,9) are cells the repo has not
beaten, so the table value there is now backed by a checked graph. Nearly every cell tried was reached within
minutes, which makes the remaining Loz values plausible. Not reproduced: {', '.join(cell(r) for r in loz_n) or 'none'}."""
p = os.path.join(HERE, 'AUDIT.md')
s = open(p).read()
s = re.sub(r'<!-- SUMMARY -->.*?<!-- /SUMMARY -->', '<!-- SUMMARY -->\n' + summary + '\n<!-- /SUMMARY -->', s, flags=re.S)
s = re.sub(r'<!-- LOZ -->.*?<!-- /LOZ -->', '<!-- LOZ -->\n' + loz + '\n<!-- /LOZ -->', s, flags=re.S)
s = re.sub(r'2\. \*\*No traceable construction:\*\* \d+ Loz cells', f'2. **No traceable construction:** {len(loz_n)} Loz cells', s)
open(p, 'w').write(s)
print('AUDIT.md filled:', len(yes), len(order), len(d8), len(none))
