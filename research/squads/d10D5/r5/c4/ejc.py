import sys, os, time
# executed inside the namespace G produced by load.py-style exec of lns3.py's top part
import numpy as np
BUDGET = int(os.environ.get('BUDGET', 4))
DEPTH = int(os.environ.get('DEPTH', 3))
TL = float(os.environ.get('TL', 300))
OUTDIR = '/home/user/degree-diameter/research/squads/d10D5/r5/c4'
NF = np.nonzero(~isfree)[0]

def sinv_now():
    s = np.empty(N, np.int64); s[sig] = np.arange(N); return s

def bads():
    sv = sinv_now(); nf = ~isfree
    rP = LM[sig][:, sig] & nf[:, None] & nf[None, :]
    nfl = nf[sv]
    rL = PM[sv][:, sv] & nfl[:, None] & nfl[None, :]
    bP = np.argwhere(np.triu(UP & ~rP)); bL = np.argwhere(np.triu(UL & ~rL))
    return [('P', int(a), int(b)) for a, b in bP] + [('L', int(a), int(b)) for a, b in bL]

def c_now():
    return len(bads())

def pt_geo_flags(a, b):
    out = []
    for c in np.nonzero(PM[a] & PM[b])[0]:
        c = int(c); L1 = int(LINE[a, c]); L2 = int(LINE[c, b])
        fl = [int(FI[a, L1]), int(FI[c, L1]), int(FI[c, L2]), int(FI[b, L2])]
        if not any(ISDEL[f] for f in fl): out += fl
    return out

def ln_geo_flags(s, t):
    out = []
    for M in np.nonzero(LM[s] & LM[t])[0]:
        M = int(M); y1 = int(PTOF[s, M]); y2 = int(PTOF[M, t])
        fl = [int(FI[y1, s]), int(FI[y1, M]), int(FI[y2, M]), int(FI[y2, t])]
        if not any(ISDEL[f] for f in fl): out += fl
    return out

def opts(pr):
    typ, a, b = pr
    sv = sinv_now()
    if typ == 'P':
        mv = [('F', f) for f in dict.fromkeys(pt_geo_flags(a, b))]
        if not isfree[a] and not isfree[b]:
            for y in NF:
                y = int(y)
                if y == a or y == b: continue
                if LM[sig[y], sig[b]]: mv.append(('S', a, y))
                if LM[sig[y], sig[a]]: mv.append(('S', b, y))
    else:
        mv = [('F', f) for f in dict.fromkeys(ln_geo_flags(a, b))]
        hs, ht = int(sv[a]), int(sv[b])
        if not isfree[hs] and not isfree[ht]:
            for y in NF:
                y = int(y)
                if y == hs or y == ht: continue
                if PM[y, ht]: mv.append(('S', hs, y))
                if PM[y, hs]: mv.append(('S', ht, y))
    return mv

def flip(f):
    nu[f] ^= 1
    st, ids = PIX; ps = ids[st[f]:st[f + 1]]
    if len(ps):
        v = unm_vec(nu, PF[ps], PV[ps]); UPv[ps] = v; UP[PA[ps], PB[ps]] = v; UP[PB[ps], PA[ps]] = v
    st, ids = LIX; ps = ids[st[f]:st[f + 1]]
    if len(ps):
        v = unm_vec(nu, LF[ps], LV[ps]); ULv[ps] = v; UL[LA[ps], LB[ps]] = v; UL[LB[ps], LA[ps]] = v

def apply(mv):
    if mv[0] == 'F': flip(mv[1])
    else:
        x, y = mv[1], mv[2]; t = sig[x]; sig[x] = sig[y]; sig[y] = t

def fmt(mv):
    return ('flip %d' % mv[1]) if mv[0] == 'F' else ('swap %d %d' % (mv[1], mv[2]))

STATS = {'nodes': 0, 'totals': 0, 'bestT': 10 ** 9, 'best': None, 'succ': None, 'seen_c': {}}
T0 = time.time()

def record(t, parts):
    if t < STATS['bestT']:
        STATS['bestT'] = t; STATS['best'] = (sig.copy(), nu.copy(), parts)
        print('  best total %d %s path=%s' % (t, parts, PATH), flush=True)

PATH = []
def dfs(depth, budget):
    if time.time() - T0 > TL: return False
    bl = bads(); c = len(bl)
    if c == 0:
        t, parts = total(sig); STATS['totals'] += 1; record(t, parts)
        if t == 0:
            STATS['succ'] = (sig.copy(), nu.copy(), list(PATH)); return True
        return False
    if depth == 0: return False
    cands = []
    for pr in bl:
        for mv in opts(pr):
            apply(mv); c2 = c_now(); STATS['nodes'] += 1; apply(mv)   # swap/flip are involutions: this undoes
            cands.append((c2, mv))
    cands.sort(key=lambda x: x[0])
    for c2, mv in cands:
        if c2 > budget: break
        apply(mv)
        t, parts = total(sig); STATS['totals'] += 1; record(t, parts)
        if t <= budget:
            PATH.append(mv)
            if dfs(depth - 1, budget): return True
            PATH.pop()
        apply(mv)
    return False

def write_state(sg, nn, fn):
    with open(fn, 'w') as f:
        f.write(' '.join(tok[:4]) + ' %d\n' % STATS_T + ' '.join(tok[5:7]) + '\n')
        f.write(' '.join(map(str, sg)) + '\n' + ' '.join(map(str, sg)) + '\n')
        f.write(' '.join(tok[7 + 2 * N:7 + 3 * N]) + '\n' + ' '.join(tok[7 + 3 * N:7 + 4 * N]) + '\n')
        f.write(' '.join(str(3 * int(v)) for v in nn) + '\n')

# sanity: incremental flips agree with full recomputation
_UPc, _ULc = UP.copy(), UL.copy()
for _f in (5, 1234, 2001):
    flip(_f)
_UPi, _ULi = UP.copy(), UL.copy()
set_unmixed(nu)
print('incremental == full:', bool((UP == _UPi).all() and (UL == _ULi).all()), flush=True)
for _f in (5, 1234, 2001): flip(_f)
set_unmixed(nu)
print('restored == original:', bool((UP == _UPc).all() and (UL == _ULc).all()), flush=True)
print('initial bads:', bads(), 'total', total(sig)[0], flush=True)
t1 = time.time(); _ = total(sig); print('total() time %.3fs' % (time.time() - t1), flush=True)
t1 = time.time(); _ = c_now(); print('c_now() time %.4fs' % (time.time() - t1), flush=True)
STATS_T = 0
t1 = time.time()
ok = dfs(DEPTH, BUDGET)
print('DFS depth %d budget %d: found=%s nodes=%d totals=%d time %.1fs bestT=%d' % (
    DEPTH, BUDGET, ok, STATS['nodes'], STATS['totals'], time.time() - t1, STATS['bestT']), flush=True)
if ok:
    sg, nn, path = STATS['succ']
    print('SUCCESS path:', [fmt(m) for m in path], flush=True)
    nu[:] = nn; sig[:] = sg; set_unmixed(nu)
    cur = 0; out = OUTDIR + '/best_d%d_b%d.lift2.sol' % (DEPTH, BUDGET)
    write(sig)
    print('wrote', out, flush=True)
elif STATS['best'] is not None:
    sg, nn, parts = STATS['best']
    out = OUTDIR + '/bestseen_d%d_b%d.lift2.sol' % (DEPTH, BUDGET)
    write_state(sg, nn, out)
    print('best seen total', STATS['bestT'], parts, 'written', out, flush=True)
