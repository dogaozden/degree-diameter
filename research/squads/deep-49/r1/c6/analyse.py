import sys, collections
fam = [l.split() for l in open('famlist.txt')]
rows = []
for line in open(sys.argv[1]):
    if not line.startswith('RES'): continue
    p = line.split()
    if p[8] != 'ok':
        rows.append(dict(idx=int(p[1]), status='skip')); continue
    idx = int(p[1]); m, kp, h, r, zeta, gG = map(int, p[2:8])
    seen, neval, best, ties = map(int, p[9:13])
    N0 = list(map(int, p[13:21]))
    rows.append(dict(idx=idx, m=m, kp=kp, h=h, r=r, zeta=zeta, gG=gG, ncand=seen, neval=neval, best=best, ties=ties, N0=N0, status='ok'))
ok = [x for x in rows if x['status'] == 'ok']
print('families', len(rows), 'ok', len(ok), 'skipped', len(rows) - len(ok))
print('ok with best<=200:', sum(1 for x in ok if x['best'] <= 200), ' <=100:', sum(1 for x in ok if x['best'] <= 100), ' <=150:', sum(1 for x in ok if x['best'] <= 150))
ok.sort(key=lambda x: (x['best'], x['m']))
def isprime(n): return n > 1 and all(n % q for q in range(2, int(n**0.5) + 1))
print('top 25 sampled (best sampled two-root far count):')
for x in ok[:25]:
    print(' m=%d kp=%d h=%d r=%d zeta=%d |G/G\'|=%d n=%d best=%d ncand=%d prime=%s' % (x['m'], x['kp'], x['h'], x['r'], x['zeta'], x['gG'], 2*x['m']*x['kp'], x['best'], x['ncand'], isprime(x['m'])))
by_h = collections.defaultdict(list)
for x in ok: by_h[x['h']].append(x['best'])
for h in sorted(by_h):
    v = sorted(by_h[h]); print('h=%d families %d min %d median %d' % (h, len(v), v[0], v[len(v)//2]))
pr = [x for x in ok if isprime(x['m'])]; cp = [x for x in ok if not isprime(x['m'])]
print('prime m: min', min(x['best'] for x in pr), ' composite m: min', min(x['best'] for x in cp))
import json
json.dump(ok, open('screen_ok.json', 'w'))
