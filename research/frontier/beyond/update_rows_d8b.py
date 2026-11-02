#!/usr/bin/env python3
"""Job raise-d8b: replace the (17..20,7) and (17..20,8) rows of BEYOND_TABLE.md with the values in ROWS below
(value, construction, check), keeping the other columns' format (% of Moore, upper bound, formula column unchanged)."""
import re, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from plan import moore, upper
ROWS = {}
def add(d, D, value, how, check): ROWS[(d, D)] = (value, how, check)
fmt = lambda x: f"{x:,}"
exec(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "rows_d8b.txt")).read())
p = os.path.join(os.path.dirname(os.path.abspath(__file__)), "BEYOND_TABLE.md")
s = open(p).read().split("\n")
for i, line in enumerate(s):
    m = re.match(r"\| \((\d+),(\d+)\) \|", line)
    if not m: continue
    key = (int(m[1]), int(m[2]))
    if key not in ROWS: continue
    cols = line.split(" | ")
    if len(cols) < 7: continue   # the small summary tables in the text
    value, how, check = ROWS[key]
    d, D = key
    cols[1] = f"**{fmt(value)}**"; cols[2] = f"{100.0 * value / moore(d, D):.2f}"; cols[3] = fmt(upper(d, D))
    cols[4] = how; cols[5] = check
    s[i] = " | ".join(cols)
open(p, "w").write("\n".join(s))
print("updated", sorted(ROWS))
