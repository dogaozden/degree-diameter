#!/usr/bin/env python3
"""prune.py LIST OUT MIN_N DONE_LOG [INFLIGHT...]: lines of LIST with order > MIN_N that are not in DONE_LOG (field 2 =
ID, or P_K_D for metacyclic lists) and not in flight."""
import sys
lst, out, mn, log = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
skip = set(sys.argv[5:])
for l in open(log):
    t = l.split()
    if t and t[0].isdigit(): skip.add(f"{t[0]}_{t[1]}")
rows = []
for l in open(lst):
    t = l.split()
    if not t or not t[0].isdigit() or int(t[0]) <= mn: continue
    key = f"{t[0]}_{t[1]}" if len(t) != 4 or not t[1].isdigit() or int(t[1]) < 31 or "_" in t[1] else None
    meta_key = f"{t[0]}_{t[1]}_{t[2]}_{t[3]}"
    if f"{t[0]}_{t[1]}" in skip or f"{t[0]}_{'_'.join(t[1:4])}" in skip: continue
    rows.append(l)
open(out, "w").write("".join(rows)); print(out, len(rows))
