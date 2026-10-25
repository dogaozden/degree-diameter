"""B(H): the bipartite graph on two copies of V(H) with x0 ~ y1 iff x = y or xy in E(H) (table-audit).
If H has maximum degree k and diameter D', B(H) is bipartite with maximum degree k+1 and diameter <= D'+1 (walk along a
shortest path and use the loop x0 ~ x1 once to fix the parity).  Input: plain edge list 'u v' per line (no header) or
apsp format with a first line n.  Usage: closed_double.py IN OUT"""
import sys
lines = [l.split() for l in open(sys.argv[1]) if l.strip() and not l.startswith('#')]
if len(lines[0]) == 1:
    n = int(lines[0][0]); E = [tuple(map(int, l)) for l in lines[1:]]
else:
    E = [tuple(map(int, l)) for l in lines]; n = 1 + max(max(e) for e in E)
Es = {(min(u, v), max(u, v)) for u, v in E}
assert len(Es) == len(E) and all(u != v for u, v in Es), 'H must be simple'
with open(sys.argv[2], 'w') as f:
    f.write(f'{2 * n}\n')
    f.writelines(f'{x} {n + x}\n' for x in range(n))
    for u, v in sorted(Es):
        f.write(f'{u} {n + v}\n{v} {n + u}\n')
print(sys.argv[2], 2 * n, n + 2 * len(Es))
