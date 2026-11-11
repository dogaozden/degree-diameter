import re, sys
rows = []
for line in open(sys.argv[1]):
    m = re.search(r'^(\d+) .*group=(.*?) N=(\d+) samples=(\d+) min=(\d+) p1=(\d+) p10=(\d+) median=(\d+)', line)
    if not m: continue
    o, grp, N, s, mn, p1, p10, med = m.groups()
    rows.append((int(p1), int(mn), int(p10), int(med), int(N), grp, o))
rows.sort()
print(len(rows), 'rows')
print('p1  min  p10  med   N      group')
for r in rows[:int(sys.argv[2]) if len(sys.argv) > 2 else 40]:
    print(f"{r[0]:4d} {r[1]:4d} {r[2]:4d} {r[3]:5d} {r[4]:6d}  {r[5]}")
