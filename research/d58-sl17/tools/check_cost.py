"""Cross-check: recompute the one-sided cost of dumped states with an independent BFS and compare with the C value."""
import sys
from sl17lib import group, parse_S, uncovered_bfs

els, idx = group()
for line in open(sys.argv[1]):
    if "|" not in line:
        continue
    head, rest = line.split("|", 1)
    cstr = head.split()[-1]
    S = parse_S(rest)
    c_ref = int(cstr)
    py = uncovered_bfs(S, els, idx, D=8)
    print(f"C cost {c_ref}  python cost {py}  {'MATCH' if py == c_ref else 'DIFF'}  S={S}")
