"""Build the degree q+3, diameter 4 graph from a 2-cover multiset of lines of Q(4,q).

The multiset (spreads/cover2_q{q}_t{size}.json, line indices into q4(q)) may repeat a line index, which means that
line is chosen twice. Every point lies on at most 2 chosen lines, so a point's degree stays at most q+1+2.

Construction (same as from_spread.py, with j = 2 point clones per ovoid point and one line clone per list entry):
  points 0..P-1, lines P..P+L-1, point clones of ovoid points, then one clone per entry of the multiset.
  Order = 2(q+1)(q^2+1) + 2(q^2+1) + |multiset|.

Usage: python3 from_cover2.py COVER.json
"""
import json, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from gq_clones import q4, lib  # noqa: E402

path = Path(sys.argv[1]); j = 2
q = int(path.stem.split('_')[1][1:])
cover = json.loads(path.read_text())
cover = cover['lines'] if isinstance(cover, dict) else cover
pts, lines, ovoid = q4(q)
load = {}
for k in cover:
    for p in lines[k]:
        load[p] = load.get(p, 0) + 1
assert max(load.values(), default=0) <= 2, 'some point lies on more than 2 chosen lines'
P, L = len(pts), len(lines)
edges = [(p, P + k) for k, Ln in enumerate(lines) for p in Ln]
base = P + L
through = {}
for k, Ln in enumerate(lines):
    for p in Ln:
        through.setdefault(p, []).append(k)
cp = [a for a in ovoid for _ in range(j)]
cl = list(cover)  # one line clone per entry: a line listed twice gets two clones
for i, a in enumerate(cp):
    edges += [(base + i, P + k) for k in through[a]]
for i, b in enumerate(cl):
    edges += [(p, base + len(cp) + i) for p in lines[b]]
n = base + len(cp) + len(cl)
ok = lib.is_valid(n, edges, q + 1 + j, 4)
print(f'q={q} j={j} cover={len(cover)}: n={n}, degree {q+1+j}, diameter 4, valid={ok}')
if ok:
    out = path.parent.parent / 'graphs' / f'gq4_cover2_q{q}_n{n}.json'
    out.write_text(json.dumps({'case': f'd{q+1+j}D4', 'value': n, 'output': [n, edges]}))
    print(out)
