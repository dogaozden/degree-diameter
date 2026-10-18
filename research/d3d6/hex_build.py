"""Build the Theorem C graph from an SA solution (hex_sa.c output) and check it.
python3 hex_build.py inst.txt sol.txt Delta [out.json]
Point copy of P in state 2 (pure): adjacent to the original lines through P (a twin).
Point copy in state 1 (mixed): for each line L through P, the original L, or the twin L' if L is pure and
the original slot of L is taken. Lines symmetric (stand-ins: original point or its twin)."""
import json, sys
sys.path.insert(0, '../../problems/bipartite_dd'); import lib

f = open(sys.argv[1]); N, K = map(int, f.readline().split())
lines = [list(map(int, f.readline().split())) for _ in range(N)]
Delta = int(sys.argv[3])
cP = {}; cL = {}
for row in open(sys.argv[2]):
    t, x, s = map(int, row.split())
    (cP if t == 0 else cL)[x] = s
thru = [[] for _ in range(N)]
for j, L in enumerate(lines):
    for p in L: thru[p].append(j)
# vertex ids: points 0..N-1, lines N..2N-1, then twins and copies
nid = [2 * N]
def new():
    nid[0] += 1; return nid[0] - 1
ptwin = {p: new() for p, s in cP.items() if s == 2}
ltwin = {j: new() for j, s in cL.items() if s == 2}
E = [(p, N + j) for j, L in enumerate(lines) for p in L]
used_line = {}   # line j -> which slots used: 'o' original, 't' twin
for p, v in ptwin.items():
    for j in thru[p]:
        E.append((v, N + j)); used_line.setdefault(j, []).append('o')
for p, s in cP.items():
    if s != 1: continue
    v = new()
    for j in thru[p]:
        u = used_line.setdefault(j, [])
        if 'o' not in u: E.append((v, N + j)); u.append('o')
        elif j in ltwin and 't' not in u: E.append((v, ltwin[j])); u.append('t')
        else: raise SystemExit(f'line {j} overfull')
used_pt = {}
for j, v in ltwin.items():
    for p in lines[j]:
        E.append((p, v)); used_pt.setdefault(p, []).append('o')
for j, s in cL.items():
    if s != 1: continue
    v = new()
    for p in lines[j]:
        u = used_pt.setdefault(p, [])
        if 'o' not in u: E.append((p, v)); u.append('o')
        elif p in ptwin and 't' not in u: E.append((ptwin[p], v)); u.append('t')
        else: raise SystemExit(f'point {p} overfull')
n = nid[0]
print('n =', n, 'max degree', lib.max_degree(n, E), flush=True)
ok = lib.is_valid(n, E, Delta, 6)
print('valid', ok)
if ok and len(sys.argv) > 4:
    json.dump({'case': f'd{Delta}D6', 'value': n, 'output': [n, E]}, open(sys.argv[4], 'w')); print('wrote', sys.argv[4])
