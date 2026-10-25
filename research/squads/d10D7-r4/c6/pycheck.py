# independent Python check of a set of points or lines of H(5): BFS in the incidence graph, all pairs at distance 6
import sys, struct
from collections import deque
H = '/home/user/degree-diameter/research/d10D7/hex/hex_q5.bin'
b = open(H, 'rb').read()
q, N, L = struct.unpack('3i', b[:12])
LP = [struct.unpack('%di' % (q + 1), b[12 + 4 * (q + 1) * i: 12 + 4 * (q + 1) * (i + 1)]) for i in range(L)]
PL = [[] for _ in range(N)]
for l, pts in enumerate(LP):
    for p in pts: PL[p].append(l)
assert all(len(x) == q + 1 for x in PL) and len(set(LP[0])) == q + 1
def dist_from(node, is_line):
    # nodes: ('p', i) or ('l', i)
    d = {(('l' if is_line else 'p'), node): 0}; dq = deque([(('l' if is_line else 'p'), node)])
    while dq:
        t, i = dq.popleft(); dv = d[(t, i)]
        nbrs = [('l', j) for j in PL[i]] if t == 'p' else [('p', j) for j in LP[i]]
        for nb in nbrs:
            if nb not in d: d[nb] = dv + 1; dq.append(nb)
    return d
ids = [int(x) for x in open(sys.argv[1]).read().split()]
kind = sys.argv[2]
assert len(set(ids)) == len(ids) and all(0 <= i < N for i in ids)
is_line = kind == 'lines'
bad = 0
for a in range(len(ids)):
    d = dist_from(ids[a], is_line)
    for c in range(a + 1, len(ids)):
        if d.get(('l' if is_line else 'p', ids[c]), -1) != 6: bad += 1
print(sys.argv[1].split('/')[-1], kind, 'size', len(ids), 'non-opposite pairs', bad, 'OK' if bad == 0 else 'FAIL')
