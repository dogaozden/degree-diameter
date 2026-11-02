#!/usr/bin/env python3
"""splice13.py: put the rows13.py rows into research/frontier/beyond/BEYOND_TABLE.md (replace the row of a cell that
is already there, append new cells before <!-- /TABLE -->), and the beyond-d13 section from SECTION_D13.md before
'## What failed'. Idempotent: rerun after new values."""
import re, subprocess
T = '../beyond/BEYOND_TABLE.md'
txt = open(T).read()
rows = subprocess.run(['python3', 'rows13.py'], capture_output=True, text=True, check=True).stdout.strip().split('\n')
head, rest = txt.split('<!-- TABLE -->\n', 1)
table, tail = rest.split('<!-- /TABLE -->', 1)
lines = table.rstrip('\n').split('\n')
for r in rows:
    cell = r.split('|')[1].strip()
    idx = [i for i, l in enumerate(lines) if l.startswith(f'| {cell} |')]
    if idx: lines[idx[0]] = r
    else: lines.append(r)
txt = head + '<!-- TABLE -->\n' + '\n'.join(lines) + '\n<!-- /TABLE -->' + tail
sec = open('SECTION_D13.md').read().rstrip('\n') + '\n'
mark = '### D = 13 at Δ = 3..10 and D = 14 at Δ = 3..8 (job beyond-d13'
if mark in txt:
    a = txt.index(mark); b = txt.index('\n## What failed', a)
    txt = txt[:a] + sec + txt[b:]
else:
    b = txt.index('\n## What failed')
    txt = txt[:b] + '\n' + sec + txt[b:]
open(T, 'w').write(txt)
print(len(rows), 'rows spliced')
