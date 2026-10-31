"""Extract the k-th state of cost <= c from a dump file into an INIT file (5 lines 'a b c d').
usage: extract_state.py dump.txt maxcost k out_init.txt"""
import sys
dump, maxc, k, out = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
rows = []
for line in open(dump):
    if "|" not in line:
        continue
    head, rest = line.split("|", 1)
    c = int(head.split()[-1])
    if c <= maxc:
        rows.append((c, rest.strip()))
c, rest = rows[k]
parts = [p.strip() for p in rest.split("|") if p.strip()]
with open(out, "w") as f:
    for p in parts:
        f.write(p + "\n")
print(f"state {k} of {len(rows)} (cost {c}) -> {out}: {parts}")
