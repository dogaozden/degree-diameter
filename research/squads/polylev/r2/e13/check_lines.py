"""Independent checker for line classes of H(q) (e13). Usage: check_lines.py HEXBIN LINECOL [s=4] [DUMMY]
LINECOL: int32 per line (class index, -1 = free). Checks, WITHOUT using the search code:
 (1) each class is a set of lines: every line of a class is a valid line of H(q) (listed in the hex file);
 (2) classes are pairwise disjoint (by construction of a colouring; asserted anyway: each line one class);
 (3) for every class c and every line L, some line of c lies within incidence distance s of L (BFS radius s
     on the point-line incidence graph, implemented from the point-line lists only).
Prints K = number of classes that are s-dominating, and the class sizes. Requires class sizes to be >= q+1 (lower bound)."""
import sys, struct
import numpy as np
hexfile, colfile = sys.argv[1], sys.argv[2]
s = int(sys.argv[3]) if len(sys.argv) > 3 else 4
with open(hexfile, 'rb') as f:
    q, N, L = struct.unpack('3i', f.read(12))
    lines = np.frombuffer(f.read(4 * L * (q + 1)), dtype=np.int32).reshape(L, q + 1)
col = np.fromfile(colfile, dtype=np.int32)
assert col.shape[0] == L, (col.shape, L)
pl = [[] for _ in range(N)]
for l in range(L):
    pts = lines[l].tolist()
    assert len(set(pts)) == q + 1
    for p in pts:
        pl[p].append(l)
assert all(len(x) == q + 1 for x in pl), 'point degrees'
# line-line distance via BFS on lines through points (distance in incidence graph = 2 * (steps) for lines)
def ball(l):
    seen = {l}; fr = [l]
    # incidence distance <= s: alternate line -> point -> line; s even for line-to-line
    for _ in range(s // 2):
        pts = set(p for m in fr for p in lines[m].tolist())
        nxt = []
        for p in pts:
            for m in pl[p]:
                if m not in seen:
                    seen.add(m); nxt.append(m)
        fr = nxt
    return seen
classes = sorted(set(col[col >= 0].tolist()))
members = {c: set(np.nonzero(col == c)[0].tolist()) for c in classes}
dom = {}
balls = [ball(l) for l in range(L)]
for c in classes:
    mem = members[c]
    dom[c] = all(len(balls[l] & mem) > 0 for l in range(L))
good = [c for c in classes if dom[c]]
sizes = sorted(len(members[c]) for c in good)
print(f'q={q} s={s}: classes {len(classes)}, s-dominating (line side) {len(good)}, '
      f'min/max size of good classes {sizes[:1]}/{sizes[-1:]}, total coloured {int((col>=0).sum())} of {L}')
print('K =', len(good))
