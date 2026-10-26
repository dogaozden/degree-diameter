import struct, numpy as np
N = 1120; MS = 40; K = 28
def load():
    d = open('/home/user/degree-diameter/research/squads/b48/r2/a12/G.bin', 'rb').read()
    return np.frombuffer(d[4:], dtype='<u2').reshape(N, N).astype(np.int64)
