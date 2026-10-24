"""hexio.py: read H(q) from hex/hex_q*.bin (research/p4/d6/hexgen.c) and write hexlift2 designs.

H = load(q)                 -> dict: q, N, lines (N lists of q+1 point ids), plines (N lists of the q+1 line ids
                               through each point, increasing), coords (N tuples of 7 ints, normalized projective
                               coordinates of the points on X0X4+X1X5+X2X6 = X3^2)
dist_from(H, v)             -> list of hexagon distances from base vertex v (points 0..N-1, lines N..2N-1)
write_design(fn, H, m1, m2, M, v, s)
    M[k][p] = line id (0..N-1) of the k-th extra edge of point p (each M[k] must be a permutation of 0..N-1)
    v[k][p] = shift code of that edge, s[p][j] = shift code of the flag (p, H['plines'][p][j]);
    a shift code c = c1 + m1*c2 means (c1 mod m1, c2 mod m2) in Z_m1 x Z_m2.
Check a design:  ./hexlift2 eval hex/hex_q5.bin DESIGN 8        (all sources; 'VALID(all sources)' = diameter <= 8)
"""
import struct, os
HERE = os.path.dirname(os.path.abspath(__file__))

def load(q):
    b = open(os.path.join(HERE, 'hex', 'hex_q%d.bin' % q), 'rb').read()
    qq, N, L = struct.unpack('<3i', b[:12])
    n = N * (q + 1)
    flat = struct.unpack('<%di' % n, b[12:12 + 4 * n])
    lines = [list(flat[i * (q + 1):(i + 1) * (q + 1)]) for i in range(N)]
    coords = [tuple(b[12 + 4 * n + 7 * i: 12 + 4 * n + 7 * i + 7]) for i in range(N)]
    plines = [[] for _ in range(N)]
    for l in range(N):
        for p in lines[l]:
            plines[p].append(l)
    return {'q': q, 'N': N, 'lines': lines, 'plines': plines, 'coords': coords}

def dist_from(H, v):
    N = H['N']; d = [-1] * (2 * N); d[v] = 0; fr = [v]
    while fr:
        nx = []
        for x in fr:
            nbrs = [N + l for l in H['plines'][x]] if x < N else H['lines'][x - N]
            for y in nbrs:
                if d[y] < 0:
                    d[y] = d[x] + 1; nx.append(y)
        fr = nx
    return d

def write_design(fn, H, m1, m2, M, v, s):
    N, q = H['N'], H['q']; t = len(M)
    for k in range(t):
        assert sorted(M[k]) == list(range(N)), 'matching %d is not a bijection' % k
    with open(fn, 'w') as f:
        f.write('%d %d %d %d\n' % (q, m1, m2, t))
        for p in range(N):
            row = []
            for k in range(t):
                row += [M[k][p], v[k][p]]
            row += list(s[p])
            f.write(' '.join(map(str, row)) + '\n')
