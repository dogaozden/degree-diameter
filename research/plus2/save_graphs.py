"""Build the +2 graph (default frame, regular filler) for q = 4..16 and save as JSON."""
import json
from pathlib import Path

from construction import pg_plane, default_frame, build, lib

OUT = Path(__file__).resolve().parent / 'graphs'
OUT.mkdir(exist_ok=True)
for q in range(4, 17):
    if not lib.is_prime_power(q):
        continue
    pts, lns = pg_plane(q)
    A, ell, P, X = default_frame(pts, lns)
    n, e = build(pts, lns, q, A, ell, P, X)
    d = q + 2
    assert lib.is_valid(n, e, d, 3)
    f = OUT / f'plus2_q{q}_d{d}_n{n}.json'
    f.write_text(json.dumps({'case': f'd{d}D3', 'construction': 'research/plus2/construction.py',
                             'q': q, 'value': n, 'output': [n, [list(x) for x in e]]}))
    print(f, n, 'moore', lib.moore_bound(d, 3))
