"""Local search (task 3b): hand the zero-change four-hat graph (construction0.py, plus a filler matching)
to the C annealer of the 376 program, which inserts one vertex per side and anneals edge swaps over ALL
edges (old incidences included).  Same engine as plus2/grow_from_plus2.py, different start.

Usage: python grow0.py q seed seconds
"""
import importlib.util
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE.parent / 'plus2'))
from construction import pg_plane, fill, lib  # noqa: E402
from construction0 import build0  # noqa: E402

spec = importlib.util.spec_from_file_location(
    'prog376', ROOT / 'records/bipartite_dd/d15D3/376-c-d3fam-w2-g002-c12.program.py')
prog = importlib.util.module_from_spec(spec)
sys.modules['lib'] = lib
spec.loader.exec_module(prog)

q, seed, secs = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3])
pts, lns = pg_plane(q)
ell = 0
A = min(set(pts) - lns[ell])
X = sorted(lns[ell])[:4]
n, e = build0(pts, lns, A, ell, X)
npts = len(pts) + 5
e = fill(n, e, q + 2, [0] * npts + [1] * (n - npts))
d = q + 2
assert lib.is_valid(n, e, d, 3)
text = lib.run_c(prog.C_SOURCE, [d, 3, seed, secs], stdin_graph=(n, e), timeout=secs + 30)
n2, e2 = lib.parse_graph_text(text)
ok = lib.is_valid(n2, e2, d, 3)
print(f'q={q} seed={seed} {secs:.0f}s: start {n}, result {n2}, valid {ok}', flush=True)
if n2 > n and ok:
    out = HERE / 'graphs' / f'grown0_q{q}_n{n2}_seed{seed}.json'
    out.write_text(json.dumps({'case': f'd{d}D3', 'value': n2, 'output': [n2, e2]}))
    print('saved', out)
