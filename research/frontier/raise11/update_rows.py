#!/usr/bin/env python3
"""update_rows.py: rewrite rows of research/frontier/beyond/BEYOND_TABLE.md for the cells listed in rows_raise11.tsv
(tab-separated: cell, value, construction, check), keeping the last column; % of M_b is recomputed."""
import re
T = "/home/user/degree-diameter/research/frontier/beyond/BEYOND_TABLE.md"
def mb(d, D): return 2 * sum((d - 1) ** i for i in range(D))
rows = [l.rstrip("\n").split("\t") for l in open("/home/user/degree-diameter/research/frontier/raise11/rows_raise11.tsv") if l.strip() and not l.startswith("#")]
lines = open(T).read().split("\n")
for cell, val, cons, chk in rows:
    d, D = map(int, cell.strip("()").split(","))
    v = int(val.replace(",", ""))
    for i, l in enumerate(lines):
        if l.startswith(f"| {cell} |"):
            parts = l.split(" | ")
            parts[1] = f"**{v:,}**"; parts[2] = f"{100 * v / mb(d, D):.2f}"; parts[4] = cons; parts[5] = chk
            lines[i] = " | ".join(parts); print("updated", cell, v); break
    else: print("no row for", cell)
open(T, "w").write("\n".join(lines))
