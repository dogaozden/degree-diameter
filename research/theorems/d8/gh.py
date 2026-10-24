"""Load the split Cayley hexagon H(q) (research/evenq/hexq.py, cached) as an incidence structure.

Vertex ids: points 0..N-1, lines N..2N-1.  H.lines[k] = points of line k, H.through[p] = lines on point p.
"""
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'research' / 'evenq'))
import hexq  # noqa: E402


def load(q):
    H = hexq.load(q, log=lambda *a: None)
    return H


def flags(H):
    """list of (point, line_vertex_id) for all flags"""
    N = H.N
    out = []
    for k in range(N):
        for p in H.lines[k]:
            out.append((int(p), N + k))
    return out


def write_base(path, NB, M1, M2, edges):
    """edges: list of (u, v, a, b) = dart u->v with voltage (a, b)"""
    with open(path, 'w') as fh:
        fh.write(f'{NB} {M1} {M2} {len(edges)}\n')
        for u, v, a, b in edges:
            fh.write(f'{u} {v} {a} {b}\n')


def distances(H):
    """all-pairs distances in the incidence graph (uint8), for small q"""
    import collections
    N = H.N
    n = 2 * N
    adj = [[] for _ in range(n)]
    for k in range(N):
        for p in H.lines[k]:
            adj[int(p)].append(N + k)
            adj[N + k].append(int(p))
    Dm = np.full((n, n), 255, dtype=np.uint8)
    for s in range(n):
        d = Dm[s]
        d[s] = 0
        dq = collections.deque([s])
        while dq:
            x = dq.popleft()
            for y in adj[x]:
                if d[y] == 255:
                    d[y] = d[x] + 1
                    dq.append(y)
    return Dm, adj
