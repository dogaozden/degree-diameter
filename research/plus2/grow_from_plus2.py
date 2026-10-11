"""Local search: hand the +2 graph to the repo's best C engine (from the 376 program) and let it
try to grow by two more vertices (insert one vertex per side, then annealed edge swaps).

Usage: python grow_from_plus2.py q seed seconds
"""
import importlib.util
import json
import sys
from pathlib import Path

ROOT = Path('/Users/dogaozden/AI_Projects/math')
sys.path.insert(0, str(Path(__file__).resolve().parent))
from construction import pg_plane, default_frame, build, lib  # noqa: E402

spec = importlib.util.spec_from_file_location(
    'prog376', ROOT / 'records/bipartite_dd/d15D3/376-c-d3fam-w2-g002-c12.program.py')
prog = importlib.util.module_from_spec(spec)
sys.modules['lib'] = lib
spec.loader.exec_module(prog)

q, seed, secs = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3])
pts, lns = pg_plane(q)
A, ell, P, X = default_frame(pts, lns)
n, e = build(pts, lns, q, A, ell, P, X)
d = q + 2
text = lib.run_c(prog.C_SOURCE, [d, 3, seed, secs], stdin_graph=(n, e), timeout=secs + 30)
n2, e2 = lib.parse_graph_text(text)
ok = lib.is_valid(n2, e2, d, 3)
print(f'q={q} seed={seed}: start {n}, result {n2}, valid {ok}', flush=True)
if n2 > n and ok:
    out = Path(__file__).resolve().parent / 'graphs' / f'grown_q{q}_n{n2}_seed{seed}.json'
    out.write_text(json.dumps({'case': f'd{d}D3', 'value': n2, 'output': [n2, e2]}))
    print('saved', out)
