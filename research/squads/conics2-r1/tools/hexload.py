"""Load a hexgen2 .bin (research/p4/d6/hex/hex_q{q}.bin): q, N, LP (lines x points), PL (points x lines), X (coords)."""
import numpy as np


def load(fn):
    b = open(fn, 'rb').read()
    q, N, Lc = (int(t) for t in np.frombuffer(b[:12], dtype=np.int32))
    LP = np.frombuffer(b[12:12 + 4 * Lc * (q + 1)], dtype=np.int32).reshape(Lc, q + 1).astype(np.int64)
    X = np.frombuffer(b[12 + 4 * Lc * (q + 1):], dtype=np.uint8).reshape(N, 7).astype(np.int64)
    fp = LP.reshape(-1); fl = np.repeat(np.arange(Lc), q + 1)
    PL = fl[np.lexsort((fl, fp))].reshape(N, q + 1)
    return q, N, LP, PL, X
