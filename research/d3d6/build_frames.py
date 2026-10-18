"""Build gadgets from a kframe output file (lines: A ell X...), repair, check, save.
python3 build_frames.py plane(q) frames.txt tag"""
import json, sys
from singer import singer_plane
from multi_gadget import lib, HERE, gadget_incidences
from repair import repair

q = int(sys.argv[1]); tag = sys.argv[3]
points, lines = singer_plane(q); Delta = q + 3
frs = []
for row in open(sys.argv[2]):
    v = list(map(int, row.split())); A, ell, X = v[0], v[1], v[2:]
    P = next(p for p in sorted(lines[ell]) if p not in X); frs.append((A, ell, P, X))
inc = gadget_incidences(lines, frs)
pts = sorted({a for a, b in inc}, key=str); lns = sorted({b for a, b in inc}, key=str)
ids = {v: i for i, v in enumerate(pts + lns)}; N = len(ids)
E = sorted((ids[a], ids[b]) for a, b in inc); side = [0] * len(pts) + [1] * len(lns)
md = lib.max_degree(N, E); print('n', N, 'maxdeg', md, flush=True)
E2 = repair(N, E, side, Delta, 3, verbose=True) if md <= Delta else None
ok = E2 is not None and lib.is_valid(N, E2, Delta, 3)
print('valid', ok)
if ok:
    out = HERE / 'graphs' / f'{tag}_q{q}_d{Delta}_n{N}.json'
    out.write_text(json.dumps({'case': f'd{Delta}D3', 'value': N, 'output': [N, E2]})); print('wrote', out)
    json.dump(frs, open(HERE / 'runs' / f'{tag}_q{q}_frames.json', 'w'))
