# check_quot.py KIND: verify that quot/q9_KIND.txt is the quotient of og_KIND.txt by quot/q9_KIND.map,
# and map the 240-vertex seed to quotient vertices (writes qseed_KIND.txt with quotient ids if it is a union of groups).
import sys
kind = sys.argv[1]
R = '/home/user/degree-diameter/research/squads/d16D7_r3/'
R2 = '/home/user/degree-diameter/research/squads/d16D7_r2/'
mp = [list(map(int, l.split())) for l in open(R + f'quot/q9_{kind}.map')]
gid = {}
for q, grp in enumerate(mp):
    for v in grp:
        assert v not in gid
        gid[v] = q
f = open(R2 + f'og_{kind}.txt')
M, E = map(int, f.readline().split())
assert M == 6504
qe = set()
bad_inner = 0
for line in f:
    a = list(map(int, line.split()))
    u = a[0]
    if u not in gid:
        continue
    for v in a[3:3 + a[2]]:
        if v in gid:
            if gid[v] == gid[u]:
                bad_inner += 1
            else:
                qe.add((gid[u], gid[v]))
# quotient file
qf = open(R + f'quot/q9_{kind}.txt')
n = int(qf.readline())
qadj = set()
wq = []
for i in range(n):
    a = list(map(int, qf.readline().split()))
    wq.append(a[0])
    for j in a[2:]:
        qadj.add((i, j))
print(kind, 'quotient n', n, 'og-derived directed edges', len(qe), 'file directed edges', len(qadj),
      'equal' if qe == qadj else 'DIFFERENT', 'inner-group edges', bad_inner)
print(' weights match map sizes:', all(wq[i] == len(mp[i]) for i in range(n)))
# seed mapping
seed = [int(x) for x in open(R + f'seed_{kind}.txt') if x.strip()]
cnt = {}
for v in seed:
    cnt[gid[v]] = cnt.get(gid[v], 0) + 1
full = all(cnt[q] == len(mp[q]) for q in cnt)
print(' seed size', len(seed), 'quotient vertices', len(cnt), 'whole groups:', full,
      'weight', sum(len(mp[q]) for q in cnt))
if full:
    open(f'qseed_{kind}.txt', 'w').write('\n'.join(map(str, sorted(cnt))) + '\n')
