import numpy as np, sys
D = '/home/user/degree-diameter/research/squads/d16D7_r2/'
def load_hex(fn=D+'data/hex_q13.bin'):
    b = open(fn, 'rb').read()
    q, N, L = np.frombuffer(b[:12], dtype=np.int32)
    q, N, L = int(q), int(N), int(L)
    LP = np.frombuffer(b[12:12 + 4 * L * (q + 1)], dtype=np.int32).reshape(L, q + 1).astype(np.int64)
    X = np.frombuffer(b[12 + 4 * L * (q + 1):], dtype=np.uint8).reshape(N, 7).astype(np.int64)
    return q, N, L, LP, X
def load_perm(fn):
    return np.fromfile(fn, dtype=np.int32).astype(np.int64)
def load_og(fn):
    with open(fn) as f:
        M, E = map(int, f.readline().split())
        rep = np.zeros(M, dtype=np.int64); nb = [None]*M
        for line in f:
            a = list(map(int, line.split()))
            rep[a[0]] = a[1]; nb[a[0]] = np.array(a[3:3+a[2]], dtype=np.int64)
    return M, E, rep, nb
