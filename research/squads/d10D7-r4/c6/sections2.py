import numpy as np, struct, itertools
H = '/home/user/degree-diameter/research/d10D7/hex/hex_q5.bin'
b = open(H, 'rb').read()
q, N, L = struct.unpack('3i', b[:12]); p = q
off = 12 + 4 * L * (q + 1)
x = np.frombuffer(b[off:off + N * 7], dtype=np.uint8).reshape(N, 7).astype(np.int64) % p
def Bform(a):
    return (x[:, 0] * a[4] + x[:, 4] * a[0] + x[:, 1] * a[5] + x[:, 5] * a[1] + x[:, 2] * a[6] + x[:, 6] * a[2] - 2 * x[:, 3] * a[3]) % p
rng = np.random.default_rng(5)
found = {}
for t in range(400):
    a = rng.integers(0, p, 7)
    Qa = (a[0]*a[4]+a[1]*a[5]+a[2]*a[6]-a[3]*a[3]) % p
    if Qa == 0: continue
    sec = np.nonzero(Bform(a) == 0)[0]
    found.setdefault(len(sec), (a.tolist(), Qa, sec))
print({k: (v[0], v[1]) for k, v in sorted(found.items())})
for k in sorted(found):
    if k in (756, 806):
        a, Qa, sec = found[k]
        open('/home/user/degree-diameter/research/squads/d10D7-r4/c6/section_%d.txt' % k, 'w').write('\n'.join(map(str, sec.tolist())) + '\n')
        print('section', k, 'pivot', a, 'Q(pivot)', Qa, 'written')
