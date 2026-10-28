"""Card c2: best relaxed unions of orbits under chosen cyclic groups and 2-generated groups of Sp(4,11)."""
import sys, os, json, time, random, collections
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5relax')
import numpy as np
from orbits import WSp, orbits_of, perm_order, best_union, Wq_pow, check_relaxed

OUT = os.path.dirname(os.path.abspath(__file__))
T_START = time.time()
P1_END = T_START + float(os.environ.get('P1', 300))
P2_END = P1_END + float(os.environ.get('P2', 120))
KMAX = 150
WANT = [61, 12, 24, 10, 20, 60, 120, 5, 11]
W = WSp(11); n = W.n
rng = random.Random(int(os.environ.get('SEED', 2024)))
log = open(os.path.join(OUT, 'search.log'), 'w')

def say(*a):
    s = ' '.join(str(x) for x in a); print(s, flush=True); log.write(s + '\n'); log.flush()

def divisors(o):
    return [d for d in range(1, o + 1) if o % d == 0]

def canon_key(lab, k):
    mins = np.array([np.flatnonzero(lab == i)[0] for i in range(k)])
    order = np.argsort(mins)
    newlab = np.empty(k, dtype=np.int64); newlab[order] = np.arange(k)
    return newlab[lab].astype(np.int16).tobytes()

def group_order(gens, cap=5000):
    idn = np.arange(n)
    key = lambda p: p.astype(np.int16).tobytes()
    seenG = {key(idn)}; frontier = [idn]
    while frontier:
        new = []
        for x in frontier:
            for g in gens:
                y = g[x]; kk = key(y)
                if kk not in seenG:
                    seenG.add(kk); new.append(y)
                    if len(seenG) > cap: return None
        frontier = new
    return len(seenG)

import multiprocessing as mp
def _mip_child(conn, lab, k, tl):
    try:
        conn.send(best_union(W, lab, k, timelimit=tl))
    except Exception as e:
        conn.send(('err', str(e)))
    conn.close()

def mip_safe(lab, k, tl):
    ctx = mp.get_context('fork')
    parent, child = ctx.Pipe(duplex=False)
    p = ctx.Process(target=_mip_child, args=(child, lab, k, tl))
    p.start(); child.close()
    res = parent.recv() if parent.poll(tl + 15) else None
    p.kill(); p.join()
    return res

seen = {}; rows = []; Ts = {}; nproc = collections.Counter()

def process(kind, gens, order_hint, deadline, desc):
    lab, k = orbits_of(gens, n)
    if k < 2 or k > KMAX: return 'skip'
    key = canon_key(lab, k)
    if key in seen: return 'dup'
    if time.time() > deadline: return None
    tl = 60.0 if k < 100 else 10.0
    tl = min(tl, max(1.0, deadline - time.time()))
    t0 = time.time()
    log.write('  MIP start k=%d tl=%.1f %s\n' % (k, tl, desc)); log.flush()
    res = mip_safe(lab, k, tl)
    el = time.time() - t0
    if res is None:
        log.write('  MIP HUNG/KILLED k=%d %s\n' % (k, desc)); log.flush()
        seen[key] = len(rows); rows.append(dict(kind=kind, group_order='?', orbits=k, best=-1, pairs=0, sizes='',
                                               time=round(el, 1), limit=tl, desc=desc + ' [MIP hung]', exact=False))
        Ts[len(rows) - 1] = []
        return 'hung'
    s, T = res
    if s > 0:
        ok, pairs = check_relaxed(W, T); assert ok, 'not relaxed!'
    else:
        pairs = 0
    sizes = collections.Counter(np.bincount(lab, minlength=k).tolist())
    sig = ' '.join('%dx%d' % (sz, c) for sz, c in sorted(sizes.items()))
    go = order_hint if order_hint is not None else group_order(gens)
    row = dict(kind=kind, group_order=go if go is not None else '>5000', orbits=k, best=s, pairs=pairs,
               sizes=sig, time=round(el, 1), limit=tl, desc=desc, exact=bool(el < tl - 0.5))
    seen[key] = len(rows); rows.append(row); Ts[len(rows) - 1] = T
    nproc[kind] += 1
    say('[%s] %s  order=%s orbits=%d best=%d pairs=%d t=%.1fs (limit %.0f) sizes=%s' %
        (kind, desc, row['group_order'], k, s, pairs, el, tl, sig))
    return 'done'

# Phase 1: cyclic groups <g^d> for random elements g whose order is divisible by a wanted number
pool = []; ne = 0; nkept = 0
while time.time() < P1_END and ne < 20000:
    g = W.random_element(rng); ne += 1
    o = perm_order(g)
    if not any(o % d == 0 for d in WANT): continue
    nkept += 1; pool.append((o, g))
    for e in divisors(o):
        if e == 1: continue
        gg = Wq_pow(g, o // e)
        r = process('cyc', [gg], e, P1_END, 'order %d element, subgroup of order %d' % (o, e))
        if r is None: break
say('phase1: elements sampled %d, kept %d, groups processed %d, %.0f s' % (ne, nkept, nproc['cyc'], time.time() - T_START))

# Phase 2: 2-generated groups <g', h> with g' a power of a pool element and h of order 2, 3 or 5
npool = 0
while time.time() < P2_END and pool:
    o, g = pool[rng.randrange(len(pool))]
    e = rng.choice([d for d in divisors(o) if d > 1]); g1 = Wq_pow(g, o // e)
    f = W.random_element(rng); of = perm_order(f)
    ps = [p for p in (2, 3, 5) if of % p == 0]
    if not ps: continue
    p = rng.choice(ps); h = Wq_pow(f, of // p)
    npool += 1
    r = process('2gen', [g1, h], None, P2_END, 'g ord %d, h ord %d' % (e, p))
    if r is None: break
say('phase2: pairs tried %d, groups processed %d, total %.0f s' % (npool, nproc['2gen'], time.time() - T_START))

# outputs
order_rows = sorted(range(len(rows)), key=lambda i: (-rows[i]['best'], rows[i]['orbits']))
with open(os.path.join(OUT, 'notes_table.tsv'), 'w') as fh:
    fh.write('rank\tkind\tgroup_order\torbits\tbest_union\tpairs\tsizes\ttime_s\tlimit_s\texact\tdesc\n')
    for r_, i in enumerate(order_rows):
        R = rows[i]
        fh.write('%d\t%s\t%s\t%d\t%d\t%d\t%s\t%s\t%.0f\t%s\t%s\n' % (r_ + 1, R['kind'], R['group_order'], R['orbits'],
                 R['best'], R['pairs'], R['sizes'], R['time'], R['limit'], 'yes' if R['exact'] else 'time-limited', R['desc']))
top = []; seen_sets = set()
for i in order_rows:
    fs = frozenset(Ts[i])
    if rows[i]['best'] <= 0 or fs in seen_sets: continue
    seen_sets.add(fs); top.append(i)
    if len(top) == 10: break
json.dump([dict(best=rows[i]['best'], group_order=rows[i]['group_order'], orbits=rows[i]['orbits'], T=sorted(Ts[i]))
           for i in top], open(os.path.join(OUT, 'unions.json'), 'w'))
for j, i in enumerate(top[:3]):
    with open(os.path.join(OUT, 'start%d.txt' % (j + 1)), 'w') as fh:
        fh.write('%d\n' % len(Ts[i])); fh.write('\n'.join(str(v) for v in sorted(Ts[i])) + '\n')
say('rows %d; top unions: %s' % (len(rows), [(rows[i]['best'], rows[i]['orbits'], rows[i]['group_order']) for i in top[:10]]))
say('total time %.0f s' % (time.time() - T_START))
