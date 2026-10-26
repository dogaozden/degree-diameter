"""Light check (no distance matrices): |S| and, per new vertex, the switch lines kept isotropic by C.  usage: python3 iso.py f.in [f2.in ...]"""
import sys
sys.path.insert(0, "/home/user/degree-diameter/research/squads/r6-d11D5/c8")
from vstats import recover_C, LINES, d_pt, n0, PTS, is_W, dinv
from collections import Counter
for path in sys.argv[1:]:
    t = open(path).read().split(); n, dg = int(t[0]), int(t[1])
    ln = [sorted(int(x) for x in t[2+l*dg:2+l*dg+dg]) for l in range(n)]
    sig = [int(x) for x in t[2+n*dg:2+n*dg+n]]
    M, C = recover_C(sig, n)
    S = set(R for R in range(n0) if is_W([C[p] for p in LINES[d_pt[R]][:2]]))
    swl = [L for L in range(n0) if ln[L] != sorted(LINES[L])]
    iso_pts = [sum(1 for L in swl if X in ln[L] and dinv[L] in S) for X in range(n0, n)]
    nsw_pts = [sum(1 for L in swl if X in ln[L]) for X in range(n0, n)]
    iso_lns = []; nsw_lns = []
    for l in range(n0, n):
        mv = [p for p in ln[l] if p < n0]
        srcs = [L for p in mv for L in swl if p in LINES[L] and p not in ln[L]]
        iso_lns.append(sum(1 for L in srcs if dinv[L] in S)); nsw_lns.append(len(srcs))
    print(f"{path}: |S|={len(S)} switch lines={len(swl)} kept isotropic={sum(1 for L in swl if dinv[L] in S)}"
          f" | new points: switch {nsw_pts} iso {iso_pts} | new lines: switch {nsw_lns} iso {iso_lns}")
