# ext.py SETFILE OUTFILE : greedy extension of an H(8) point set (ids) by any H(8) points opposite to all members.
import sys, struct, numpy as np
HEX = '/home/user/degree-diameter/research/d10D7/hex/hex_q8.bin'
MUL8 = np.zeros((8, 8), dtype=np.int64)
for x in range(8):
    for y in range(8):
        a = [(x >> i) & 1 for i in range(3)]; b = [(y >> i) & 1 for i in range(3)]
        r = [0] * 5
        for i in range(3):
            for j in range(3): r[i + j] ^= a[i] & b[j]
        for k in (4, 3):
            if r[k]: r[k] = 0; r[k - 3] ^= 1; r[k - 2] ^= 1
        MUL8[x, y] = r[0] | (r[1] << 1) | (r[2] << 2)
raw = open(HEX, 'rb').read()
N = struct.unpack('<iii', raw[:12])[1]
X = np.frombuffer(raw[12 + N * 36:12 + N * 36 + N * 7], dtype=np.uint8).reshape(N, 7).astype(np.int64)
def B(p, s):  # p: array (N,7), s: 7-vector
    return (MUL8[p[:, 0], s[4]] ^ MUL8[p[:, 4], s[0]] ^ MUL8[p[:, 1], s[5]] ^ MUL8[p[:, 5], s[1]]
            ^ MUL8[p[:, 2], s[6]] ^ MUL8[p[:, 6], s[2]])
S = [int(x) for x in open(sys.argv[1]).read().split()]
assert len(set(S)) == len(S)
ok = np.ones(N, dtype=bool)
for s in S: ok &= (B(X, X[s]) != 0)
ok[S] = False
free = np.nonzero(ok)[0]
print('set size', len(S), ' free outside points (opposite to all members):', len(free))
cur = list(S)
cand = list(free)
added = []
while cand:
    f = cand[0]; added.append(f); cur.append(f)
    cand = [c for c in cand[1:] if B(X[[c]], X[f])[0] != 0]
print('greedy extension added', len(added), 'final size', len(cur))
open(sys.argv[2], 'w').write('\n'.join(map(str, cur)) + '\n')
