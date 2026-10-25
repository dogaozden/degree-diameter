# hexio.py: load research/d10D7/hex/hex_qQ.bin (int32 q,N,L; L*(q+1) int32 line->point ids; N*7 uint8 coords).
import numpy as np

def load_hex(path):
    raw = open(path, 'rb').read()
    q, N, L = np.frombuffer(raw[:12], dtype='<i4')
    q, N, L = int(q), int(N), int(L)
    off = 12
    lines = np.frombuffer(raw, dtype='<i4', count=L * (q + 1), offset=off).reshape(L, q + 1).astype(np.int64)
    off += 4 * L * (q + 1)
    coords = np.frombuffer(raw, dtype=np.uint8, count=N * 7, offset=off).reshape(N, 7).astype(np.int64)
    return q, N, lines, coords

def point_lines(q, N, lines):
    """pl[p] = array of q+1 line ids through point p."""
    L = lines.shape[0]
    cnt = np.zeros(N, dtype=np.int64)
    pl = np.zeros((N, q + 1), dtype=np.int64)
    for l in range(L):
        for p in lines[l]:
            pl[p, cnt[p]] = l
            cnt[p] += 1
    assert (cnt == q + 1).all()
    return pl

def bfs_dist(q, N, lines, pl, src_point):
    """distances in the incidence graph: points 0..N-1, lines N..N+L-1. Returns point distances (array N)."""
    L = lines.shape[0]
    dist = np.full(N + L, -1, dtype=np.int64)
    dist[src_point] = 0
    frontier = [src_point]
    d = 0
    while frontier:
        d += 1
        nxt = []
        for v in frontier:
            if v < N:
                for l in pl[v]:
                    w = N + l
                    if dist[w] < 0:
                        dist[w] = d
                        nxt.append(w)
            else:
                for p in lines[v - N]:
                    if dist[p] < 0:
                        dist[p] = d
                        nxt.append(p)
        frontier = nxt
    return dist[:N], dist[N:]

def bform(x, y, q):
    """polar form of X0X4+X1X5+X2X6-X3^2 (odd q: B = Q(x+y)-Q(x)-Q(y))."""
    return (x[0]*y[4] + x[4]*y[0] + x[1]*y[5] + x[5]*y[1] + x[2]*y[6] + x[6]*y[2] - 2*x[3]*y[3]) % q

def qform(x, q):
    return (x[0]*x[4] + x[1]*x[5] + x[2]*x[6] - x[3]*x[3]) % q
