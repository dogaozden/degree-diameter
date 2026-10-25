"""Shared helpers for the q=3 test bed (card c8). Vertex ids: main (v,i) -> i*728 + v, v<364 point, v=364+l line.
Hubs: 3640 + index. Edge files: first line n, then 'a b' per line (apsp.c format)."""
import struct, array, sys
from collections import deque
HEX = '/home/user/degree-diameter/research/squads/d12D7-r2/c8/hex/hex_q3.bin'
PHI = '/home/user/degree-diameter/research/squads/d12D7-r2/c8/dual/h3.phi'
SPREAD = '/home/user/degree-diameter/research/squads/d12D7-r2/c8/sets_h3_spread.txt'
q = 3; N = 364; Q1 = 4; NL = 5; B = 2 * N   # B = 728 vertices per level
def load_hex(fn=HEX):
    raw = open(fn, 'rb').read(); qq, n, L = struct.unpack('3i', raw[:12]); assert qq == 3 and n == N and L == N
    a = array.array('i'); a.frombytes(raw[12:12 + 4 * L * Q1])
    return [tuple(a[l * Q1:(l + 1) * Q1]) for l in range(L)]
def load_phi(fn=PHI):
    a = array.array('i'); a.frombytes(open(fn, 'rb').read()); phi = list(a)
    M = [phi[p] - N for p in range(N)]
    assert sorted(M) == list(range(N))
    return M
def load_spread(fn=SPREAD):
    return [int(x) for x in open(fn).read().split()]
def ID(v, i): return i * B + v
def main_edges(LP, M, freed):
    """Main graph edges: incidence (level-wise) + matchings (p,i)-(M(p),i+1),(M(p),i+2) for non-freed p."""
    E = []
    for l in range(N):
        for p in LP[l]:
            for i in range(NL): E.append((ID(p, i), ID(N + l, i)))
    for p in range(N):
        if p in freed: continue
        for i in range(NL):
            E.append((ID(p, i), ID(N + M[p], (i + 1) % NL)))
            E.append((ID(p, i), ID(N + M[p], (i + 2) % NL)))
    return E
def write_edges(fn, n, E):
    with open(fn, 'w') as f:
        f.write('%d\n' % n)
        f.write(''.join('%d %d\n' % e for e in E))
def dist_from(adj, s):
    n = len(adj); d = [-1] * n; d[s] = 0; dq = deque([s])
    while dq:
        x = dq.popleft()
        for y in adj[x]:
            if d[y] < 0: d[y] = d[x] + 1; dq.append(y)
    return d
def adjlist(n, E):
    adj = [[] for _ in range(n)]
    for a, b in E: adj[a].append(b); adj[b].append(a)
    return adj
