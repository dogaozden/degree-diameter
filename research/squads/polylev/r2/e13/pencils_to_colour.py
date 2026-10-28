"""Turn a set of pairwise non-collinear points (point ids, .npy) into a line colouring: line l gets the index of the
unique chosen point on it (-1 if none). Asserts that every line contains at most one chosen point.
Usage: pencils_to_colour.py HEXBIN POINTS.npy OUT.bin"""
import sys, struct
import numpy as np
hexfile, ptsfile, out = sys.argv[1], sys.argv[2], sys.argv[3]
with open(hexfile, 'rb') as f:
    q, N, L = struct.unpack('3i', f.read(12))
    lines = np.frombuffer(f.read(4 * L * (q + 1)), dtype=np.int32).reshape(L, q + 1)
S = np.load(ptsfile).tolist()
idx = {p: i for i, p in enumerate(S)}
col = np.full(L, -1, dtype=np.int32)
for l in range(L):
    hit = [idx[int(p)] for p in lines[l] if int(p) in idx]
    assert len(hit) <= 1, ('two points of the set on line', l)
    if hit:
        col[l] = hit[0]
col.tofile(out)
print('points', len(S), 'lines covered', int((col >= 0).sum()), 'of', L, '-> classes', len(S))
