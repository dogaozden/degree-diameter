"""Independent check of the census claim "168 / 506 are the largest bipartite cubic vertex-transitive graphs of
diameter 7 / 9" (table-audit-2).  Input: JSON pages from the MathDataHub cvt collection (Potocnik-Spiga-Verret census
of cubic vertex-transitive graphs, all graphs on <= 1280 vertices), with the graph in sparse6.  Only the stored
order, bipartite flag and graph are used; the diameter is recomputed here (a vertex-transitive graph has diameter =
eccentricity of any vertex, so one BFS per graph; we also check 3-regularity and bipartiteness).
usage: cvt_check.py D PAGE.json [PAGE.json ...]   prints the largest graph of diameter <= D found and a summary."""
import json, sys
from collections import deque


def sparse6(s):
    s = s.strip()
    assert s[0] == ':'
    data = [ord(c) - 63 for c in s[1:]]
    if data[0] < 63:
        n, data = data[0], data[1:]
    elif data[1] < 63:
        n = (data[1] << 12) | (data[2] << 6) | data[3]; data = data[4:]
    else:
        n = 0
        for x in data[2:8]: n = (n << 6) | x
        data = data[8:]
    k = max(1, (n - 1).bit_length())
    bits = []
    for x in data:
        for i in range(5, -1, -1): bits.append((x >> i) & 1)
    E = []; v = 0; i = 0
    while i + 1 + k <= len(bits):
        b = bits[i]; x = 0
        for j in range(k): x = (x << 1) | bits[i + 1 + j]
        i += 1 + k
        if b: v += 1
        if v >= n: break
        if x > v: v = x
        else: E.append((x, v))
    return n, E


def ecc0(n, E):
    adj = [[] for _ in range(n)]
    for u, w in E: adj[u].append(w); adj[w].append(u)
    assert all(len(a) == 3 for a in adj), 'not cubic'
    d = [-1] * n; d[0] = 0; qq = deque([0])
    while qq:
        x = qq.popleft()
        for y in adj[x]:
            if d[y] < 0: d[y] = d[x] + 1; qq.append(y)
            elif (d[y] - d[x]) % 2 == 0: raise ValueError('odd cycle')
    assert min(d) >= 0, 'disconnected'
    return max(d)


D = int(sys.argv[1]); best = None; cnt = 0; bydiam = {}
for path in sys.argv[2:]:
    for r in json.load(open(path))['results']:
        n, E = sparse6(r['graph'])
        assert n == r['order'], (n, r['order'])
        e = ecc0(n, E); cnt += 1
        bydiam[e] = bydiam.get(e, 0) + 1
        if e <= D and (best is None or n > best[0]): best = (n, r.get('cvt_index'), e)
        if r.get('diameter') is not None and r['diameter'] != e: print('db diameter differs:', r['order'], r.get('cvt_index'), r['diameter'], e)
print(f'{cnt} graphs checked (cubic, connected, bipartite); diameters found: {dict(sorted(bydiam.items()))}')
print(f'largest with diameter <= {D}: {best}')
