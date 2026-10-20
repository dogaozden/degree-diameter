"""Write hs.c instances.  usage: python3 export_inst.py q mode [e]   (mode: st | po | free | pq; e: F^4 model, pq not supported)
st/po/free: vertices = points of W(3,q); hyperedges = t.i. lines outside S (cap 1) and lines of S (cap 2 / 1 / none).
pq: vertices = antipodal pairs (z, r), index z*t + r (z = q^2 for infinity); hyperedges = spread lines (cap 1) and
    the images of the t.i. lines outside S (cap 1).
Also writes runs/map_{mode}_q{q}.json (vertex -> point list) for decoding.
"""
import json
import sys
from pathlib import Path

from w3k import W3

q, mode = int(sys.argv[1]), sys.argv[2]
e = int(sys.argv[3]) if len(sys.argv) > 3 else -1   # e >= 0: F^4 model with spread sigma = p^e (w3f.py)
if e >= 0:
    from w3f import W3F
    W = W3F(q, e)
else:
    W = W3(q)
Q = q * q
t = (q + 1) // 2
here = Path(__file__).resolve().parent
edges = []
if mode in ('st', 'po', 'free'):
    nv = len(W.pts)
    for j, L in enumerate(W.lines):
        if W.is_spread_line[j]:
            if mode == 'free':
                continue
            edges.append((2 if mode == 'st' else 1, L))
        else:
            edges.append((1, L))
    vmap = [[p] for p in range(nv)]
else:
    def zi(p):
        a, b = W.pts[p]
        if a == 0:
            return Q, int(W.log[b]) % (q + 1)
        return int(W.mul[b, W.K.inv(a)]), int(W.log[a]) % (q + 1)
    nv = (Q + 1) * t
    vmap = [[] for _ in range(nv)]
    for p in range(len(W.pts)):
        z, i = zi(p)
        vmap[z * t + i % t].append(p)
    assert all(len(v) == 2 for v in vmap)
    for z in range(Q + 1):
        edges.append((1, [z * t + r for r in range(t)]))
    for j, L in enumerate(W.lines):
        if W.is_spread_line[j]:
            continue
        vs = sorted({(lambda zz: zz[0] * t + zz[1] % t)(zi(p)) for p in L})
        assert len(vs) == q + 1
        edges.append((1, vs))
tag = f'_e{e}' if e >= 0 else ''
out = here / 'runs' / f'inst_{mode}_q{q}{tag}.txt'
with open(out, 'w') as f:
    f.write(f'{nv} {len(edges)}\n')
    for c, L in edges:
        f.write(f'{c} {len(L)} ' + ' '.join(map(str, L)) + '\n')
(here / 'runs' / f'map_{mode}_q{q}{tag}.json').write_text(json.dumps(vmap))
print('wrote', out, nv, len(edges))
