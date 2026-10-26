"""Write the relaxed-set input for relaxed.c (format: n, then 'k nb1 f1 nb2 f2 ...' per point) for W(q).
f = 1 iff the line joining the two collinear points is a line of the regular spread S (forbidden pair)."""
import sys
q = int(sys.argv[1])
rd = open('W%d_lines.txt' % q).read().split('\n')
npts, nl = map(int, rd[0].split())
lines = [tuple(map(int, rd[1 + i].split())) for i in range(nl)]
S = set(map(int, open('W%d_spread.txt' % q).read().split()[1:]))
lid = {}
for i, l in enumerate(lines):
    for a in l:
        for b in l:
            if a != b: lid[(a, b)] = i
nb = [[] for _ in range(npts)]
for (a, b), i in lid.items(): nb[a].append((b, 1 if i in S else 0))
with open('relax_W%d.in' % q, 'w') as f:
    f.write('%d\n' % npts)
    for p in range(npts):
        f.write('%d %s\n' % (len(nb[p]), ' '.join('%d %d' % x for x in nb[p])))
print('written', 'points', npts, 'forbidden pairs (ordered)', sum(x[1] for p in range(npts) for x in nb[p]))
