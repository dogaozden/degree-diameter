"""Regular completion of Corollary B1/C1 graphs (D = 4).
W(3,q), q odd, Delta = q+1+j with j even: j copies of every spread line (= j ovoid copies in Q(4,q)) and j/2 copies of
a Singer 2-ovoid C_a u C_{q-a} (= j/2 Singer 2-covers of Q(4,q)). All originals then have degree Delta; the copies have
degree q+1. Both copy sets have j(q^2+1) vertices, on opposite sides, so adding a j-regular bipartite graph between them
(j cyclic perfect matchings) makes the graph Delta-regular. Adding edges cannot increase distances.
usage: build_regular.py q j [OUT.json]"""
import json, sys
from pathlib import Path
from w3k import W3, orbits
import groups
sys.path.insert(0, str(Path(__file__).resolve().parents[3] / 'problems' / 'bipartite_dd'))
import lib
q, j = int(sys.argv[1]), int(sys.argv[2])
assert j % 2 == 0
W = W3(q); n = len(W.pts); nl = len(W.lines)
orbs, of = orbits(n, groups.gens(W, 'ns:1'))
X = None
for a in range(len(orbs)):
    for b in range(a + 1, len(orbs)):
        S = set(orbs[a]) | set(orbs[b])
        if all(sum(p in S for p in L) == 2 for L in W.lines):
            X = sorted(S); break
    if X: break
assert X and len(X) == 2 * (q * q + 1)
edges = [(p, n + l) for l, L in enumerate(W.lines) for p in L]
v = n + nl
line_copies, point_copies = [], []
for L in W.spread:
    for _ in range(j):
        edges += [(p, v) for p in L]; line_copies.append(v); v += 1
for _ in range(j // 2):
    for m in X:
        edges += [(v, n + l) for l in W.on[m]]; point_copies.append(v); v += 1
N = len(line_copies)
assert N == len(point_copies) == j * (q * q + 1)
for k in range(j):  # j disjoint perfect matchings (shifts 0..j-1)
    edges += [(point_copies[i], line_copies[(i + k) % N]) for i in range(N)]
deg = [0] * v
for a, b in edges: deg[a] += 1; deg[b] += 1
D = q + 1 + j
print(f'q={q} j={j} Delta={D} order={v} expected={2*D*(q*q+1)} degrees={sorted(set(deg))}')
ok = lib.is_valid(v, edges, D, 4)
print('valid', ok)
if ok and len(sys.argv) > 3:
    Path(sys.argv[3]).write_text(json.dumps({'case': f'd{D}D4', 'value': v, 'output': [v, [list(e) for e in edges]]}))
