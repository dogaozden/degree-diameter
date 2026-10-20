"""Read hex/hex_q{q}.bin written by hexgen.c. Returns (q, N, lines, coords)."""
import numpy as np


def load(q, path=None):
    path = path or f'hex/hex_q{q}.bin'
    with open(path, 'rb') as f:
        hdr = np.frombuffer(f.read(12), dtype=np.int32)
        q, N, L = map(int, hdr)
        lines = np.frombuffer(f.read(4 * L * (q + 1)), dtype=np.int32).reshape(L, q + 1)
        crd = np.frombuffer(f.read(7 * N), dtype=np.uint8).reshape(N, 7)
    return q, N, lines, crd
