# swap12.py SETFILE: check (1,2)-swap local optimality of an H(8) opposite set (full point set, numpy).
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
raw = open(HEX, 'rb').read(); N = struct.unpack('<iii', raw[:12])[1]
X = np.frombuffer(raw[12 + N * 36:12 + N * 36 + N * 7], dtype=np.uint8).reshape(N, 7).astype(np.int64)
def Bvec(p, s):  # p: (k,7) array, s: (7,) vector -> B(p, s)
    return (MUL8[p[:, 0], s[4]] ^ MUL8[p[:, 4], s[0]] ^ MUL8[p[:, 1], s[5]] ^ MUL8[p[:, 5], s[1]]
            ^ MUL8[p[:, 2], s[6]] ^ MUL8[p[:, 6], s[2]])
S = [int(x) for x in open(sys.argv[1]).read().split()]
inS = np.zeros(N, dtype=bool); inS[S] = True
conf = np.zeros(N, dtype=np.int64)
for s in S:
    conf += (Bvec(X, X[s]) == 0)
conf[S] -= 1  # a member is counted once for itself (B(x,x)=0)
print('set', len(S), 'conf histogram of non-members (0,1,2):',
      [(c, int(((conf == c) & ~inS).sum())) for c in (0, 1, 2)])
found = 0; pairs_checked = 0
for s in S:
    T = np.nonzero((conf == 1) & ~inS & (Bvec(X, X[s]) == 0))[0]
    for a in range(len(T)):
        for b in range(a + 1, len(T)):
            pairs_checked += 1
            if Bvec(X[[T[a]]], X[T[b]])[0] != 0:
                found += 1
                if found <= 3: print('(1,2)-swap: remove', s, 'add', int(T[a]), int(T[b]))
print('one-tight pairs checked', pairs_checked, 'improving (1,2)-swaps found', found)
