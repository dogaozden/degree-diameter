"""Write P(W(q),x) as an instance file for ls_cap.
python3 export_inst.py q [mult] -> runs/as_q{q}.inst, or runs/as_q{q}_x{mult}.inst with each point repeated mult
times (copy c of point p has index c*q^3 + p), so ls_cap then searches multisets."""
import sys
from pathlib import Path
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from as_gq import build
q = int(sys.argv[1])
mult = int(sys.argv[2]) if len(sys.argv) > 2 else 1
F, pts, lines = build(q)
n = len(pts)
name = f'as_q{q}.inst' if mult == 1 else f'as_q{q}_x{mult}.inst'
with open(HERE / 'runs' / name, 'w') as f:
    f.write(f'{n * mult} {len(lines)}\n')
    for L in lines:
        P = [c * n + p for c in range(mult) for p in L]
        f.write(f'{len(P)} ' + ' '.join(map(str, P)) + '\n')
