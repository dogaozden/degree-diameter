"""Independent validity check of a relaxed set: usage check_relaxed.py Q "i j k ..." (point ids).
Checks: each point has <=1 collinear neighbour in T; no two collinear points of T lie on a regular-spread line."""
import sys
q = int(sys.argv[1]); T = list(map(int, sys.argv[2].split()))
rd = open('W%d_lines.txt' % q).read().split('\n')
npts, nl = map(int, rd[0].split())
lines = [tuple(map(int, rd[1 + i].split())) for i in range(nl)]
S = set(map(int, open('W%d_spread.txt' % q).read().split()[1:]))
assert len(set(T)) == len(T)
Ts = set(T)
def col(a, b): return any(a in l and b in l for l in lines)
for t in T:
    nbrs = [u for u in T if u != t and col(t, u)]
    assert len(nbrs) <= 1, (t, nbrs)
    for u in nbrs:
        assert not any(i in S and t in lines[i] and u in lines[i] for i in range(nl)), ('spread pair', t, u)
print('VALID relaxed set in W(%d): |T| = %d' % (q, len(T)))
