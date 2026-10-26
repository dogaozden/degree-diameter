import re, math, sys, collections
from math import gcd
rows = []
for line in open('/home/user/degree-diameter/research/squads/b48/r1/scan_meta_1092_1120.txt'):
    m_ = re.match(r'(\d+) (\d+) (\d+) (\d+) (\d+) :: .*best=(\d+)', line)
    if not m_: continue
    N, m, k, r, o, best = map(int, m_.groups())
    rows.append((N, m, k, r, o, best))
print("rows", len(rows))
def factor(n):
    f = {}; d = 2
    while d*d <= n:
        while n % d == 0: f[d] = f.get(d,0)+1; n//=d
        d += 1
    if n > 1: f[n] = f.get(n,0)+1
    return f
def feats(N, m, k, r, o):
    g = gcd(r-1, m)
    # verify ord
    rr = 1; oo = 0
    while True:
        rr = rr*r % m; oo += 1
        if rr == 1 % m: break
    cent = g * (k // oo)
    fm = factor(m); fk = factor(k)
    return dict(N=N, m=m, k=k, r=r, o=o, g=g, cent=cent, nonfaith=k//o,
                fixedratio=g/m, mprimes=len(fm), kprimes=len(fk),
                msqfree=all(e==1 for e in fm.values()), kpow2=(k & (k-1))==0,
                kodd=k%2==1, modd=m%2==1, kprime=len(fk)==1 and list(fk.values())[0]==1,
                gcd_mk=gcd(m,k), derived=m//g, r_1mod_k=(r%k), nonabelian=(o>1 or True))
data = []
for (N,m,k,r,o,best) in rows:
    f = feats(N,m,k,r,o); f['best']=best; data.append(f)
# order check
bad = [(d['m'],d['k'],d['r'],d['o']) for d in data if d['o'] != 0 and False]
def stats(key, fn=None):
    buckets = collections.defaultdict(list)
    for d in data:
        buckets[fn(d) if fn else d[key]].append(d['best'])
    out = []
    for b, v in sorted(buckets.items(), key=lambda t: (sum(t[1])/len(t[1]))):
        v2 = sorted(v)
        out.append((str(b), len(v), round(sum(v)/len(v),1), v2[0], v2[len(v2)//2]))
    return out
for name, fn in [('k', lambda d: d['k']), ('o (ord r)', lambda d: d['o']), ('k/ord (nonfaith)', lambda d: d['nonfaith']),
                 ('g=gcd(r-1,m)', lambda d: d['g']), ('cent', lambda d: d['cent']), ('mprimes', lambda d: d['mprimes']),
                 ('msqfree', lambda d: d['msqfree']), ('kprime', lambda d: d['kprime']),
                 ('kpow2', lambda d: d['kpow2']), ('kodd', lambda d: d['kodd']), ('modd', lambda d: d['modd']),
                 ('N', lambda d: d['N'])]:
    print("==", name)
    for row in stats(None, fn)[:25]:
        print("  ", row)
