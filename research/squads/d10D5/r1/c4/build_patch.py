"""build_patch.py GQBIN DMFILE FREEFILE BFILE OUT: edge list (first line n) of the hub graph for a lift2-format DM
solution (sigma, mv0=1, mv1=4, nu in {0,3}) with freed points FREE, H=2 hubs per side per freed point (numbered as in
build_hub.py) and hub-hub edges from BFILE (lines 'a b': L-hub a = i*H+s, P-hub b = j*H+t)."""
import struct, sys, hashlib
gq, dmf, freef, bf, out = sys.argv[1:6]
with open(gq, 'rb') as f:
    q, N, L = struct.unpack('3i', f.read(12)); Q1 = q + 1
    lines = [list(struct.unpack(f'{Q1}i', f.read(4 * Q1))) for _ in range(L)]
tok = open(dmf).read().split()
sig = list(map(int, tok[7:7 + N])); mv0 = list(map(int, tok[7 + 2 * N:7 + 3 * N])); mv1 = list(map(int, tok[7 + 3 * N:7 + 4 * N]))
nu = list(map(int, tok[7 + 4 * N:7 + 4 * N + N * Q1]))
free = list(map(int, open(freef).read().split()))
H = 2; M = 6
assert sorted(sig) == list(range(N))
E = []
for l, ps in enumerate(lines):
    for k, p in enumerate(ps):
        for h in range(M): E.append((p * M + h, (N + l) * M + (h + nu[l * Q1 + k]) % M))
fs = set(free)
for p in range(N):
    if p in fs: continue
    for h in range(M):
        E.append((p * M + h, (N + sig[p]) * M + (h + mv0[p]) % M)); E.append((p * M + h, (N + sig[p]) * M + (h + mv1[p]) % M))
hub = 2 * N * M
for p in free:
    for x in (p, N + sig[p]):
        for _ in range(H):
            for h in range(M): E.append((hub, x * M + h))
            hub += 1
base = 2 * N * M
for ln in open(bf):
    t = ln.split()
    if not t: continue
    a, b = int(t[0]), int(t[1])
    E.append((base + (a // H) * 2 * H + a % H, base + (b // H) * 2 * H + H + b % H))
body = f'{hub}\n' + ''.join(f'{a} {b}\n' for a, b in E)
open(out, 'w').write(body)
deg = [0] * hub
for a, b in E: deg[a] += 1; deg[b] += 1
print('n', hub, 'edges', len(E), 'max degree', max(deg), 'min degree', min(deg), 'sha256', hashlib.sha256(body.encode()).hexdigest()[:16])
