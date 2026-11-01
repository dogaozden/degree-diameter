#!/usr/bin/env python3
"""splice15.py: put the rows15.py rows into research/frontier/beyond/BEYOND_TABLE.md (replace the row of a cell that is
already there, append new cells before <!-- /TABLE -->), the beyond-d15 section SECTION_D15.md before '## What failed',
the extension note after the beyond-d13 one, and a summary bullet. Idempotent: rerun after new values."""
import subprocess, re
T = '../beyond/BEYOND_TABLE.md'
txt = open(T).read()
rows = subprocess.run(['python3', 'rows15.py'], capture_output=True, text=True, check=True).stdout.strip().split('\n')
head, rest = txt.split('<!-- TABLE -->\n', 1)
table, tail = rest.split('<!-- /TABLE -->', 1)
lines = table.rstrip('\n').split('\n')
new = 0
for r in rows:
    cell = r.split('|')[1].strip()
    idx = [i for i, l in enumerate(lines) if l.startswith(f'| {cell} |')]
    if idx: lines[idx[0]] = r
    else: lines.append(r); new += 1
txt = head + '<!-- TABLE -->\n' + '\n'.join(lines) + '\n<!-- /TABLE -->' + tail
# title count
ncells = sum(1 for l in lines if l.startswith('| ('))
txt = re.sub(r'^# Beyond the 2013 table: first values for \d+ new cells', f'# Beyond the 2013 table: first values for {ncells} new cells', txt, count=1, flags=re.M)
ext = ('Extended 2026-11-01 by job beyond-d15 (branch claude/new-cells-d15-d16-fpj633): eight more cells, D = 15 and D = 16 at\n'
       'Δ = 3..6; see the section "D = 15 and D = 16 at Δ = 3..6" below.\n')
if 'job beyond-d15' not in txt.split('## Summary')[0]:
    a = txt.index('## Summary'); txt = txt[:a] + ext + '\n' + txt[a:]
bullet = '<!-- D15 -->\n' + open('SUMMARY_D15.md').read().rstrip('\n') + '\n<!-- /D15 -->\n'
if '<!-- D15 -->' in txt:
    a = txt.index('<!-- D15 -->'); b = txt.index('<!-- /D15 -->\n') + len('<!-- /D15 -->\n')
    txt = txt[:a] + bullet + txt[b:]
else:
    a = txt.index('## Upper bounds'); txt = txt[:a].rstrip('\n') + '\n' + bullet + '\n' + txt[a:]
sec = open('SECTION_D15.md').read().rstrip('\n') + '\n'
mark = '### D = 15 and D = 16 at Δ = 3..6 (job beyond-d15'
if mark in txt:
    a = txt.index(mark); b = txt.index('\n## What failed', a)
    txt = txt[:a] + sec + txt[b:]
else:
    b = txt.index('\n## What failed')
    txt = txt[:b] + '\n' + sec + txt[b:]
open(T, 'w').write(txt)
print(len(rows), 'rows,', new, 'new; table now', ncells, 'cells')
