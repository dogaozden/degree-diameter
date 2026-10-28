"""Independent certifier (does not import hexlib): parses the raw hexagon file, then checks that the chosen point ids
are distinct and valid, and that no line of H(11) contains two chosen points.
usage: certify.py HEXBIN POINTFILE"""
import sys, struct, numpy as np
hexf, ptf = sys.argv[1], sys.argv[2]
with open(hexf, 'rb') as f:
    q, N, L = struct.unpack('3i', f.read(12))
    lines = np.frombuffer(f.read(4 * L * (q + 1)), dtype=np.int32).reshape(L, q + 1)
assert lines.min() >= 0 and lines.max() < N
ptsel = [int(x) for x in open(ptf).read().split()]
S = np.array(ptsel, dtype=np.int64)
assert len(np.unique(S)) == len(S), 'duplicate points'
assert S.min() >= 0 and S.max() < N, 'point id out of range'
chosen = np.zeros(N, dtype=np.int64); chosen[S] = 1
per_line = chosen[lines].sum(axis=1)           # chosen points on each line
bad = int((per_line > 1).sum())
print('q', q, 'N', N, 'L', L, 'chosen', len(S), 'lines with >=2 chosen points', bad,
      'VALID' if bad == 0 else 'INVALID')
