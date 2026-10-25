import sys
from collections import Counter
q = sys.argv[1]
with open(q) as f:
    n = int(f.readline())
    w = [0]*n; nb = [None]*n
    for i in range(n):
        a = list(map(int, f.readline().split()))
        w[i] = a[0]; nb[i] = a[2:2+a[1]]
        assert len(nb[i]) == a[1]
sym = sum(1 for v in range(n) for u in nb[v] if v not in nb[u])
selfl = sum(1 for v in range(n) if v in nb[v])
dup = sum(1 for v in range(n) if len(set(nb[v])) != len(nb[v]))
cnt = Counter(w)
heavy = [v for v in range(n) if w[v] == max(w)]
hset = set(heavy)
hdeg = [sum(1 for u in nb[v] if u in hset) for v in heavy]
print('n=%d sumw=%d weights=%s asym=%d selfloops=%d dupnb=%d' % (n, sum(w), dict(cnt), sym, selfl, dup))
print('heavy H=%d induced deg min/avg/max=%d/%.1f/%d' % (len(heavy), min(hdeg), sum(hdeg)/len(hdeg), max(hdeg)))
lightdeg = [sum(1 for u in nb[v] if u in hset) for v in range(n) if w[v] < max(w)]
print('light->heavy degree min/avg/max=%d/%.1f/%d' % (min(lightdeg), sum(lightdeg)/len(lightdeg), max(lightdeg)))
