"""Turn an annealer output (d16_sa.c) into a (16,3) graph JSON and run scripts/verify_record.py on it.
Usage: python3 d16_finish.py OUT.txt   -> graphs/d16_n<order>.json (only if verify passes)."""
import json, subprocess, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
src = Path(sys.argv[1])
R, C = map(int, src.open().readline().split())
edges = [[r, R + c] for r, c in (map(int, ln.split()) for ln in src.open().readlines()[1:] if ln.strip())]
n = R + C
out = HERE / 'graphs' / f'd16_n{n}.json'
out.write_text(json.dumps({'case': 'd16D3', 'value': n, 'output': [n, edges]}))
print('wrote', out, 'n =', n, 'edges =', len(edges))
res = subprocess.run([sys.executable, 'scripts/verify_record.py', str(out), '16', '3'], cwd=ROOT, capture_output=True, text=True)
print(res.stdout[-2000:]); print(res.stderr[-1000:]); print('exit', res.returncode)
