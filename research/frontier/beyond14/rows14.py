#!/usr/bin/env python3
"""rows14.py: replace the D = 14 rows of research/frontier/beyond/BEYOND_TABLE.md with this job's values (ROWS below),
insert rows for cells that are not there yet ((9,14), (10,14)) after the (8,14) row, and put SECTION_D14.md before the
section "## What failed". Run from the repository root. Idempotent: an existing beyond-d14 section is replaced."""
import re

def Mb(d, D):
    return 2 * sum((d - 1) ** i for i in range(D))

ROWS = {}   # (d, D) -> (value, construction, check, family)
exec(open('research/frontier/beyond14/rows14_data.py').read())

p = 'research/frontier/beyond/BEYOND_TABLE.md'
s = open(p).read()
lines = s.split('\n')
out = []
done = set()
for line in lines:
    m = re.match(r'^\| \((\d+),(\d+)\) \|', line)
    if m and (int(m.group(1)), int(m.group(2))) in ROWS:
        key = (int(m.group(1)), int(m.group(2)))
        out.append(None); out[-1] = key; done.add(key)
        continue
    out.append(line)

def row(key):
    d, D = key
    v, cons, chk, fam = ROWS[key]
    mb = Mb(d, D)
    return f"| ({d},{D}) | **{v:,}** | {100 * v / mb:.2f} | {mb - 6:,} | {cons} | {chk} | {fam} |"

res = []
for item in out:
    if isinstance(item, tuple):
        res.append(row(item))
        if item == (8, 14):
            for k in sorted(ROWS):
                if k not in done and k[1] == 14 and k[0] > 8:
                    res.append(row(k)); done.add(k)
    else:
        res.append(item)
s = '\n'.join(res)
sec = open('research/frontier/beyond14/SECTION_D14.md').read().rstrip('\n') + '\n'
start = s.find('### D = 14 raises at')
if start >= 0:
    end = s.find('\n## ', start)
    s = s[:start] + sec + s[end:]
else:
    i = s.find('## What failed')
    s = s[:i] + sec + '\n' + s[i:]
open(p, 'w').write(s)
print('rows written:', sorted(done))
