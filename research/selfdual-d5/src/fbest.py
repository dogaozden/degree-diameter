#!/usr/bin/env python3
"""fbest.py DIR...: best energy per (group, record, type) over the sdtabu .out files in DIR (fmeta/, gapf/, tabu/,
deep/), sorted by best; one line "best group rec f m steps secs" each.  env MAXB (default 6) limits the list."""
import glob, os, sys
maxb = int(os.environ.get("MAXB", 6)); rows = []
for d in sys.argv[1:]:
    for f in glob.glob(os.path.join(d, "*.out")):
        g = os.path.basename(f)[:-4]
        for l in open(f):
            t = l.split()
            if t and t[0] == "TABU":
                b = int(t[t.index("best") + 1])
                if b <= maxb:
                    rows.append((b, g, t[2], t[t.index("f") + 1], t[t.index("m") + 1], t[t.index("steps") + 1], t[t.index("secs") + 1]))
for r in sorted(rows, key=lambda r: (r[0], r[1])): print(*r)
