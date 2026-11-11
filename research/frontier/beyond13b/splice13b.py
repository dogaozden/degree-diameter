#!/usr/bin/env python3
"""splice13b.py: put the rows13b.py rows into research/frontier/beyond/BEYOND_TABLE.md (replacing the row of the
cell) and SECTION_D13B.md before '## What failed'. Idempotent."""
import subprocess
T = '../beyond/BEYOND_TABLE.md'
txt = open(T).read()
rows = [r for r in subprocess.run(['python3', 'rows13b.py'], capture_output=True, text=True, check=True).stdout.split('\n') if r]
head, rest = txt.split('<!-- TABLE -->\n', 1)
table, tail = rest.split('<!-- /TABLE -->', 1)
lines = table.rstrip('\n').split('\n')
for r in rows:
    cell = r.split('|')[1].strip()
    idx = [i for i, l in enumerate(lines) if l.startswith(f'| {cell} |')]
    if idx: lines[idx[0]] = r
    else: lines.append(r)
txt = head + '<!-- TABLE -->\n' + '\n'.join(lines) + '\n<!-- /TABLE -->' + tail
sec = open('SECTION_D13B.md').read().rstrip('\n') + '\n'
mark = '### D = 13 at Δ = 5..10, second pass (job beyond-d13b'
if mark in txt:
    a = txt.index(mark); b = txt.index('\n## What failed', a)
    txt = txt[:a] + sec + txt[b:]
else:
    b = txt.index('\n## What failed')
    txt = txt[:b] + '\n' + sec + txt[b:]
open(T, 'w').write(txt)
print(len(rows), 'rows spliced')
