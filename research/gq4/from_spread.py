"""Build the gq_clones.py graph from a saved partial spread (spreads/spread_q{q}_s{s}.json, line indices into q4(q)).

Usage: python3 from_spread.py SPREAD.json [j]   (j copies per ovoid point and per spread line; degree q+1+j)
"""
import json, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from gq_clones import q4, lib  # noqa: E402

path = Path(sys.argv[1]); j = int(sys.argv[2]) if len(sys.argv) > 2 else 1
q = int(path.stem.split('_')[1][1:])
spread = json.loads(path.read_text())
spread = spread['lines'] if isinstance(spread, dict) else spread
pts, lines, ovoid = q4(q)
assert all(not (lines[a] & lines[b]) for i, a in enumerate(spread) for b in spread[i + 1:]), 'lines not disjoint'
P, L = len(pts), len(lines)
edges = [(p, P + k) for k, Ln in enumerate(lines) for p in Ln]
base = P + L
through = {}
for k, Ln in enumerate(lines):
    for p in Ln:
        through.setdefault(p, []).append(k)
cp = [a for a in ovoid for _ in range(j)]
cl = [b for b in spread for _ in range(j)]
for i, a in enumerate(cp):
    edges += [(base + i, P + k) for k in through[a]]
for i, b in enumerate(cl):
    edges += [(p, base + len(cp) + i) for p in lines[b]]
n = base + len(cp) + len(cl)
ok = lib.is_valid(n, edges, q + 1 + j, 4)
print(f'q={q} j={j} s={len(spread)}: n={n}, degree {q+1+j}, diameter 4, valid={ok}')
if ok:
    out = path.parent.parent / 'graphs' / f'gq4_q{q}{"_j" + str(j) if j > 1 else ""}_n{n}.json'
    out.write_text(json.dumps({'case': f'd{q+1+j}D4', 'value': n, 'output': [n, edges]}))
    print(out)
