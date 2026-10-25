"""build_hub.py GQBIN SOL OUT: rebuild the hub graph of a dmhub solution as an edge list for apsp.c (independent of
dmhub.c).  Lift vertex (x, h) = 6x + h, x < N points, N <= x < 2N lines (line l is x = N + l); flag (p, l) with
voltage nu gives (p,h) ~ (l,h+nu); each non-freed point p gives (p,h) ~ (sigma(p), h+mv0(p)) and (sigma(p), h+mv1(p));
freed point i gets hc_i line-side hubs joined to (p,0..5) and hc_i point-side hubs joined to (sigma(p),0..5).
Per-flag counts hc_i come from the 'hlist' line (HLIST), default H.  Hub numbering: flag i occupies 2*sum_{j<i} hc_j
vertices from 12N: its line-side hubs first, then its point-side hubs.  Prints n, edge count, sha256 of the written file."""
import struct, sys, hashlib
gq, sol, out = sys.argv[1:4]
with open(gq, 'rb') as f:
    q, N, L = struct.unpack('3i', f.read(12)); Q1 = q + 1
    lines = [list(struct.unpack(f'{Q1}i', f.read(4 * Q1))) for _ in range(L)]
rows = {}
for ln in open(sol):
    t = ln.split()
    if t: rows[t[0]] = t[1:]
H = int(rows['dmhub'][3]); free = list(map(int, rows.get('free', [])))
hc = [int(x) for x in rows['hlist']] if 'hlist' in rows else [H] * len(free)
assert len(hc) == len(free)
ho = []; acc = 0
for h in hc: ho.append(acc); acc += h
hf, hs = [], []
for i, h in enumerate(hc):
    for s in range(h): hf.append(i); hs.append(s)
sig = list(map(int, rows['sigma'])); mv0 = list(map(int, rows['mv0'])); mv1 = list(map(int, rows['mv1'])); nu = list(map(int, rows['nu']))
assert sorted(sig) == list(range(N)) and len(nu) == N * Q1
M = 6; E = []
for l, ps in enumerate(lines):
    for k, p in enumerate(ps):
        for h in range(M): E.append((p * M + h, (N + l) * M + (h + nu[l * Q1 + k]) % M))
fs = set(free)
for p in range(N):
    if p in fs: continue
    for h in range(M):
        E.append((p * M + h, (N + sig[p]) * M + (h + mv0[p]) % M)); E.append((p * M + h, (N + sig[p]) * M + (h + mv1[p]) % M))
hub = 2 * N * M
for i, p in enumerate(free):
    for x in (p, N + sig[p]):
        for _ in range(hc[i]):
            for h in range(M): E.append((hub, x * M + h))
            hub += 1
hg = list(map(int, rows.get('hubgraph', [])))
base = 2 * N * M
for e in range(0, len(hg), 2):
    a, b = hg[e], hg[e + 1]
    E.append((base + 2 * ho[hf[a]] + hs[a], base + 2 * ho[hf[b]] + hc[hf[b]] + hs[b]))
body = f'{hub}\n' + ''.join(f'{a} {b}\n' for a, b in E)
open(out, 'w').write(body)
print('n', hub, 'edges', len(E), 'sha256', hashlib.sha256(body.encode()).hexdigest())
