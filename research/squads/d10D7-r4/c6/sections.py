import numpy as np, struct, collections
H = '/home/user/degree-diameter/research/d10D7/hex/hex_q5.bin'
b = open(H, 'rb').read()
q, N, L = struct.unpack('3i', b[:12]); p = q
off = 12 + 4 * L * (q + 1)
C = np.frombuffer(b[off:off + N * 7], dtype=np.uint8).reshape(N, 7).astype(np.int64) % p
x = C
Qv = (x[:, 0] * x[:, 4] + x[:, 1] * x[:, 5] + x[:, 2] * x[:, 6] - x[:, 3] * x[:, 3]) % p
print('points on quadric Q:', int((Qv == 0).sum()), 'of', N, 'coords range', C.min(), C.max())
def B(a):
    return (x[:, 0] * a[4] + x[:, 4] * a[0] + x[:, 1] * a[5] + x[:, 5] * a[1] + x[:, 2] * a[6] + x[:, 6] * a[2] - 2 * x[:, 3] * a[3]) % p
res = {}
for idx in range(N):
    a = C[idx]
    if (a[0]*a[4]+a[1]*a[5]+a[2]*a[6]-a[3]*a[3]) % p == 0: continue   # need non-singular a
    sec = np.nonzero(B(a) == 0)[0]
    res.setdefault(len(sec), []).append(idx)
    if len(res) >= 6 and all(len(v) > 0 for v in res.values()) and idx > 500: break
print({k: len(v) for k, v in sorted(res.items())})
for k in (756, 806):
    if k in res:
        a = res[k][0]
        sec = np.nonzero(B(C[a]) == 0)[0]
        open('/home/user/degree-diameter/research/squads/d10D7-r4/c6/section_%d.txt' % k, 'w').write('\n'.join(map(str, sec)) + '\n')
        print('wrote section', k, 'with pivot', a, 'size', len(sec))
