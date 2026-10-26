#!/usr/bin/env python3
"""satlns.py STATE.sol C0.lift2.sol "FDSET" OUT.lift2.sol: exact SAT neighbourhoods for the coset-0 problem with sigma
fixed.  The full instance (satnu.py encoding) is built once; each step frees the nu of a ball of flags around the bad
pairs (flags on their geodesics, then flags on geodesics of pairs touching those, ...) and fixes every other flag to its
current value by assumptions.  SAT = a complete solution (written to OUT); UNSAT = no fix inside that ball (grow it).
env: SIZES (ball sizes to try, e.g. "800 1200 1600 2000"), CONFL (conflict limit per call, via set_option), SEED."""
import sys, os, time, random
R4 = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
st, c0, fds, out = [os.path.abspath(x) if i != 2 else x for i, x in enumerate(sys.argv[1:5])]
os.chdir(R4); sys.path.insert(0, R4)
sys.argv = ['lns3.py', st, c0, fds, out]; os.environ['SECS'] = '0'
exec(open('lns3.py').read().split("best = cur; t0 = time.time()")[0])
import pycryptosat
rng = random.Random(int(os.environ.get('SEED', 1)))
bp, bl, rp, rl = bad_ids(sig)
s = pycryptosat.Solver(threads=1)
nxt = [N * 8 + 1]
for Fl, Vl, routed in ((PF, PV, rp), (LF, LV, rl)):
    for q in np.nonzero(~routed)[0]:
        ps = []
        for g in range(8):
            if not Vl[q, g]: continue
            v = nxt[0]; nxt[0] += 1; s.add_xor_clause([v] + [int(f) + 1 for f in Fl[q, g]], False); ps.append(v)
        s.add_clause(ps); s.add_clause([-v for v in ps])
print('instance built', nxt[0] - 1, 'vars', flush=True)
# ball growth over the flag-pair incidence (unrouted pairs only)
def pairs_of(f):
    out_ = []
    for (IX, rr, side) in ((PIX, rp, True), (LIX, rl, False)):
        st_, ids = IX; ps = ids[st_[f]:st_[f + 1]]; out_ += [(side, int(q)) for q in ps[~rr[ps]]]
    return out_
def ball(K):
    seeds = [(True, int(q)) for q in bp] + [(False, int(q)) for q in bl]
    inb = set(); order = []; frontier = seeds; seenp = set(seeds)
    while frontier and len(order) < K:
        nf_ = []
        rng.shuffle(frontier)
        for side, q in frontier:
            for f in geo_flags(side, q):
                if ISDEL[f] or f in inb: continue
                inb.add(f); order.append(f)
                if len(order) >= K: break
                for pq in pairs_of(f):
                    if pq not in seenp: seenp.add(pq); nf_.append(pq)
            if len(order) >= K: break
        frontier = nf_
    return inb
if os.environ.get('CONFL'): s.set_option('maxconfl', os.environ['CONFL']) if False else None
for K in [int(x) for x in os.environ.get('SIZES', '800 1200 1600 2000 2400').split()]:
    B = ball(K)
    assum = [(f + 1) if nu[f] else -(f + 1) for f in range(N * 8) if f not in B and not ISDEL[f]]
    t0 = time.time(); sat, sol = s.solve(assumptions=assum)
    print('ball', len(B), 'fixed', len(assum), 'result', sat, '%.1fs' % (time.time() - t0), flush=True)
    if sat:
        for f in range(N * 8): nu[f] = 1 if sol[f + 1] else 0
        set_unmixed(nu); print('exact after SAT:', total(sig), flush=True); cur = total(sig)[0]; write(sig); break
