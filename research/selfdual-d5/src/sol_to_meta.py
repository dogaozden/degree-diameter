#!/usr/bin/env python3
"""sol_to_meta.py OUT EXP [N]: the N-th (default first) SOL line of an sdtabu/sdtabu2 output on a meta_export.py
export, written in metacyclic coordinates: element index e = i*k + j is x^i y^j = (i,j).  EXP is the export's .exp
line (meta_export output).  Prints m k r, beta (u,t,v) of the record (beta(x) = x^u, beta(y) = x^t y^v; record 0 is
beta = identity, records 1.. are the 'reps' in order), and S as "i,j i,j ...", ready for
records/build_metacyclic_haar.py and records/make_meta_record.sh."""
import re, sys
out, exp = sys.argv[1], sys.argv[2]; nth = int(sys.argv[3]) if len(sys.argv) > 3 else 1
e = open(exp).read().split()
m, k, r = int(e[e.index("m") + 1]), int(e[e.index("k") + 1]), int(e[e.index("r") + 1])
reps = [tuple(map(int, t.split(","))) for t in e[e.index("reps") + 1:]]
sols = [l.split() for l in open(out) if l.startswith("SOL")]
tag, S = sols[nth - 1][1], list(map(int, sols[nth - 1][2:]))
rec = int(re.match(r"r(\d+)_alpha", tag).group(1))
u, t, v = (1, 0, 1) if rec == 0 else reps[rec - 1]
print(f"m {m} k {k} r {r} tag {tag} beta {u} {t} {v}")
print(" ".join(f"{x // k},{x % k}" for x in S))
