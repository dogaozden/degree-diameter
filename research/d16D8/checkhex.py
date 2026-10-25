# checkhex.py: check that a baselift base file is the flags of H(q) (hex/hex_qQ.bin) + exactly two point->line
# perfect matchings (every base vertex gets 2 extra edges, each from a point to a line).
import sys, struct
fn, q = sys.argv[1], int(sys.argv[2])
b = open('/home/user/degree-diameter/research/d16D8/hex/hex_q%d.bin' % q, 'rb').read()
q_, N, L = struct.unpack('<3i', b[:12])
lp = struct.unpack('<%di' % (L * (q + 1)), b[12:12 + 4 * L * (q + 1)])
flags = set((lp[l * (q + 1) + j], N + l) for l in range(L) for j in range(q + 1))
f = open(fn); V, m, E = map(int, f.readline().split())
seen = set(); ext = []
for _ in range(E):
    x, y, c, cl = map(int, f.readline().split())
    if x > y: x, y = y, x
    if (x, y) in flags and (x, y) not in seen: seen.add((x, y))
    else: ext.append((x, y))
deg = [0] * (2 * N)
for x, y in ext: deg[x] += 1; deg[y] += 1
ok = V == 2 * N and len(seen) == len(flags) and set(deg) == {2} and all(x < N <= y for x, y in ext)
print('V', V, 'm', m, 'flags', len(seen), '/', len(flags), 'extra', len(ext), 'extra-degree set', set(deg), 'OK' if ok else 'BAD')
