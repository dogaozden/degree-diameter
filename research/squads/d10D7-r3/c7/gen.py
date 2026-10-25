"""c7 generator: X(M) for the generalized hexagon H(q) (default q=5) plus local modifications.
Vertex ids: point (p,i) = i*2N + p, line (l,i) = i*2N + N + l, i in {0,1,2}; new vertices are >= 6N.
Base edges: hexagon (p,i)~(l,i) for p on l; extra (p,i)~(M(p),i+1).
Modifications act on the extra edges: delete_extra(p,i) removes (p,i)~(M(p),i+1)."""
import struct, sys, os
import numpy as np

HEX = '/home/user/degree-diameter/research/d10D7/hex/hex_q%d.bin'

def load_hex(q=5):
    with open(HEX % q, 'rb') as f:
        qq, N, N2 = struct.unpack('3i', f.read(12))
        LP = np.frombuffer(f.read(4 * N2 * (qq + 1)), dtype=np.int32).reshape(N2, qq + 1).copy()
    return N, LP

def base_edges(N, LP, M):
    """Return list of (u,v) for X(M) without modifications, plus index dict for extra edges."""
    E = []
    for i in range(3):
        for l in range(N):
            for p in LP[l]:
                E.append((i * 2 * N + int(p), i * 2 * N + N + l))
    for i in range(3):
        for p in range(N):
            E.append((i * 2 * N + p, ((i + 1) % 3) * 2 * N + N + int(M[p])))
    return E

def extra_id(N, M, p, i):
    """The extra edge of point-vertex (p,i): returns the pair it forms (u,v) in base ids."""
    return (i * 2 * N + p, ((i + 1) % 3) * 2 * N + N + int(M[p]))

def build(N, LP, M, deleted, new_edges, t_new):
    """deleted: list of (p,i) whose extra edge is removed. new_edges: list of (u,v) using new ids 6N..6N+t_new-1
    or base ids. Returns (n, edges)."""
    E = base_edges(N, LP, M)
    dele = set(extra_id(N, M, p, i) for (p, i) in deleted)
    # extra edges are the last 3N of the base list; drop deleted ones
    out = []
    for (u, v) in E:
        if (u, v) in dele:
            continue
        out.append((u, v))
    assert len(out) == len(E) - len(dele), 'deleted edge not found'
    out.extend(new_edges)
    return 6 * N + t_new, out

def write(n, edges, fn):
    with open(fn, 'w') as f:
        f.write('%d\n' % n)
        f.write(''.join('%d %d\n' % (u, v) for (u, v) in edges))
    return fn
