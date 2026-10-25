import sys, struct
from collections import deque
fn, sp = sys.argv[1], sys.argv[2]
raw = open(fn, 'rb').read(); q, N, L = struct.unpack('3i', raw[:12])
import array
LP = array.array('i'); LP.frombytes(raw[12:12 + 4 * L * (q + 1)]); LP = [LP[l*(q+1):(l+1)*(q+1)] for l in range(L)]
lines = [int(x) for x in open(sp).read().split()]
# incidence graph BFS distances between lines
PL = [[] for _ in range(N)]
for l in range(L):
    for p in LP[l]: PL[p].append(l)
def line_dist_from(l0):
    # distance in the incidence graph between line l0 and every line (points at odd steps)
    dist = {('l', l0): 0}; dq = deque([('l', l0)])
    while dq:
        t, x = dq.popleft(); d = dist[(t, x)]
        if t == 'l':
            for p in LP[x]:
                if ('p', p) not in dist: dist[('p', p)] = d + 1; dq.append(('p', p))
        else:
            for l in PL[x]:
                if ('l', l) not in dist: dist[('l', l)] = d + 1; dq.append(('l', l))
    return dist
ok = True
mind = 99
for i, a in enumerate(lines):
    d = line_dist_from(a)
    for b in lines[i+1:]:
        dd = d[('l', b)]
        mind = min(mind, dd)
        if dd != 6: ok = False
print('lines', len(lines), 'distinct', len(set(lines)), 'min pairwise incidence distance', mind, 'pairwise opposite:', ok)
pts = set(p for l in lines for p in LP[l])
print('points covered', len(pts))
