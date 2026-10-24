import struct, sys
from collections import deque
HEX = '/home/user/degree-diameter/research/squads/exp2/r1/c6/hex/hex_q5.bin'
def load_hex(fn=HEX):
    with open(fn, 'rb') as f:
        q, N, L = struct.unpack('<iii', f.read(12))
        Q1 = q + 1
        lp = struct.unpack('<%di' % (L * Q1), f.read(4 * L * Q1))
    LP = [list(lp[l*Q1:(l+1)*Q1]) for l in range(L)]
    PL = [[] for _ in range(N)]
    for l in range(L):
        for p in LP[l]:
            PL[p].append(l)
    return q, N, LP, PL
def hbfs(N, LP, PL, x, isline):
    # incidence-graph distances: points 0..N-1, lines N..2N-1
    d = [-1] * (2 * N)
    s = N + x if isline else x
    d[s] = 0
    dq = deque([s])
    while dq:
        v = dq.popleft()
        if v < N:
            for l in PL[v]:
                w = N + l
                if d[w] < 0:
                    d[w] = d[v] + 1; dq.append(w)
        else:
            for p in LP[v - N]:
                if d[p] < 0:
                    d[p] = d[v] + 1; dq.append(p)
    return d
