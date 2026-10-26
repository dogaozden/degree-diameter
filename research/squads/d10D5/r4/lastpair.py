#!/usr/bin/env python3
"""lastpair.py STATE.sol C0.lift2.sol "FDSET" OUT.lift2.sol: finisher for a state with few bad pairs.  For every flag f
on a bad pair's geodesics (cheapest first), flip f; the pairs this newly unmixes without a route must get routes:
build sigma neighbourhoods from exactly those pairs (both movable endpoints + owners of lines meeting the other
endpoint's line) and run lns2-style exact sigma steps (coverage, D1, all unmixed pairs' routes); keep the flip if the
exact total drops.  env: REPAIRS (steps per flip), STEP (s), SIZE, SEED, MAXF (flags tried per round)."""
import sys, os, random, time
import numpy as np
st, c0, fds, out = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4]
sys.argv = ['lns3.py', st, c0, fds, out]
os.environ.setdefault('SECS', '0')
exec(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'lns3.py')).read().split("best = cur; t0 = time.time()")[0])
rng = random.Random(int(os.environ.get('SEED', 1)))
REP = int(os.environ.get('REPAIRS', 6)); STP = float(os.environ.get('STEP', 20)); SZ = int(os.environ.get('SIZE', 60))
MAXF = int(os.environ.get('MAXF', 40)); NE = int(os.environ.get('NENAB', 10))
def nb_for(pairs, sig):
    sinv = np.empty(N, np.int64); sinv[sig] = np.arange(N); S = []
    for s2, q in pairs:
        if s2: a, b = int(PA[q]), int(PB[q])
        else: a, b = int(sinv[LA[q]]), int(sinv[LB[q]])
        if isfree[a] or isfree[b]: continue
        for x, o in ((a, b), (b, a)):
            if banned[x]: continue
            if s2: en = [int(sinv[M]) for M in np.nonzero(LM[sig[o]])[0]]
            else: en = [int(w) for w in np.nonzero(PM[o])[0]]
            rng.shuffle(en); S += [x] + [e for e in en if not banned[e]][:NE]
    S = [x for x in dict.fromkeys(S) if not banned[x]]
    kz = KZ; S2 = []
    for x in S:
        if second[x]:
            if kz <= 0: continue
            kz -= 1
        S2.append(x)
    S2 = S2[:SZ]
    rest = [x for x in range(N) if not banned[x] and not second[x] and x not in set(S2)]; rng.shuffle(rest)
    return S2 + rest[:max(0, SZ - len(S2)) // 3]
best = cur; t0 = time.time()
while cur > 0 and time.time() - t0 < float(os.environ.get('TOTAL', 1200)):
    bp, bl, rp, rl = bad_ids(sig)
    cands = []
    for side, ids in ((True, bp), (False, bl)):
        for pid in ids:
            for f in dict.fromkeys(geo_flags(side, int(pid))):
                if ISDEL[f]: continue
                c = crit(f, sig, rp, rl)
                hard = sum(1 for s2, q in c if (isfree[PA[q]] or isfree[PB[q]]) if s2) + sum(1 for s2, q in c if not s2 and (int(LA[q]) in set(int(sig[p]) for p in F) or int(LB[q]) in set(int(sig[p]) for p in F)))
                cands.append((hard, len(c) + rng.random(), f, c))
    cands.sort(key=lambda t: (t[0], t[1]))
    improved = False
    for hard, nc, f, c in cands[:MAXF]:
        nu_old = nu.copy(); nu[f] ^= 1; set_unmixed(nu)
        c1, p1 = total(sig); bsig = sig.copy(); bc = c1
        for r in range(REP):
            if bc < cur: break
            bp2, bl2, _, _ = bad_ids(bsig)
            pairs = [(True, int(q)) for q in bp2] + [(False, int(q)) for q in bl2]
            S = nb_for(pairs, bsig)
            res, info = step(bsig, S, STP, rng.randint(1, 10 ** 6))
            if res is None: continue
            new, _ = res; c2, p2 = total(new)
            if c2 < bc: bc, bsig = c2, new
        print('flag %d (hard %d, crit %d): after flip %d -> repaired %d (cur %d) %.0fs' % (f, hard, int(nc), c1, bc, cur, time.time() - t0), flush=True)
        if bc < cur:
            sig = bsig; cur = bc; improved = True
            write(sig); print('IMPROVED to', cur, total(sig)[1], flush=True); break
        nu[:] = nu_old; set_unmixed(nu)
    if not improved: print('no flag improves; stop'); break
print('final', cur, total(sig)[1])
