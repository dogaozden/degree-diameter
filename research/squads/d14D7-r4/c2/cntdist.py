import sys
from collections import Counter
rows = [list(map(int, l.split())) for l in open('/home/user/degree-diameter/research/cell147/data/E11.map') if l.strip()]
Q = 11
X = [[c % Q for c in r[2:9]] for r in rows]
hexid = [r[0] for r in rows]
pos = {h: i for i, h in enumerate(hexid)}
def orth(a, b):
    v = a[0]*b[4] + a[4]*b[0] + a[1]*b[5] + a[5]*b[1] + a[2]*b[6] + a[6]*b[2] - 2*a[3]*b[3]
    return v % Q == 0
for fn in sys.argv[1:]:
    S = [pos[int(l.split()[0])] for l in open(fn) if l.strip()]
    inS = set(S)
    cnt = [0] * len(rows)
    for s in S:
        for v in range(len(rows)):
            if v != s and orth(X[s], X[v]):
                cnt[v] += 1
    out = [cnt[v] for v in range(len(rows)) if v not in inS]
    c = Counter(out)
    print(fn, 'size', len(S), 'min cnt outside', min(out), 'count cnt==8', c[8], 'count cnt<=9', sum(1 for x in out if x <= 9), 'mean', round(sum(out)/len(out), 2))
