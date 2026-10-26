"""Write W(q) in 'spread-group' form for relaxed_bb.c: line 1 = n; then per point: group g (its regular-spread line),
k, and its k collinear neighbours. Verifies the structural facts used: every point lies on exactly one spread line,
and every point off a spread line is collinear with exactly one point of that line (GQ axiom)."""
import sys
q = int(sys.argv[1])
rd = open('W%d_lines.txt' % q).read().split('\n')
npts, nl = map(int, rd[0].split())
lines = [tuple(map(int, rd[1 + i].split())) for i in range(nl)]
S = list(map(int, open('W%d_spread.txt' % q).read().split()[1:]))
grp = [-1] * npts
for g, i in enumerate(S):
    for p in lines[i]:
        assert grp[p] == -1
        grp[p] = g
assert min(grp) >= 0
col = [set() for _ in range(npts)]
for l in lines:
    for a in l:
        for b in l:
            if a != b:
                col[a].add(b)
for p in range(npts):
    for g in range(len(S)):
        if g != grp[p]:
            assert sum(1 for x in col[p] if grp[x] == g) == 1
with open('relax_groups_W%d.txt' % q, 'w') as f:
    f.write('%d\n' % npts)
    for p in range(npts):
        f.write('%d %d %s\n' % (grp[p], len(col[p]), ' '.join(map(str, sorted(col[p])))))
print('groups', len(S), 'points', npts, 'ok')
