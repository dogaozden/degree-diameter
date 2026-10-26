#!/usr/bin/env python3
"""satball.py STATE.sol C0.lift2.sol "FDSET" OUT.lift2.sol: exact SAT decision for the coset-0 problem with sigma fixed,
nu free on a ball of flags around the bad pairs and fixed elsewhere.  Reduced encoding: a pair whose geodesics without
ball flags already have both parities is dropped; fixed flags are folded into the XOR right-hand sides.  SAT = complete
solution (written to OUT).  env: SIZES (ball sizes), SEED, THREADS."""
import sys, os, time, random
R4 = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
st, c0, fds, out = [os.path.abspath(x) if i != 2 else x for i, x in enumerate(sys.argv[1:5])]
os.chdir(R4); sys.path.insert(0, R4)
sys.argv = ['lns3.py', st, c0, fds, out]; os.environ['SECS'] = '0'
exec(open('lns3.py').read().split("best = cur; t0 = time.time()")[0])
import pycryptosat
rng = random.Random(int(os.environ.get('SEED', 1)))
bp, bl, rp, rl = bad_ids(sig)
def pairs_of(f):
    o = []
    for (IX, rr, side) in ((PIX, rp, True), (LIX, rl, False)):
        st_, ids = IX; ps = ids[st_[f]:st_[f + 1]]; o += [(side, int(q)) for q in ps[~rr[ps]]]
    return o
def ball(K):
    seeds = [(True, int(q)) for q in bp] + [(False, int(q)) for q in bl]
    inb = set(); frontier = seeds; seenp = set(seeds)
    while frontier and len(inb) < K:
        nf_ = []; rng.shuffle(frontier)
        for side, q in frontier:
            for f in geo_flags(side, q):
                if ISDEL[f] or f in inb: continue
                inb.add(f)
                if len(inb) >= K: break
                for pq in pairs_of(f):
                    if pq not in seenp: seenp.add(pq); nf_.append(pq)
            if len(inb) >= K: break
        frontier = nf_
    return inb
def solve_ball(B):
    inB = np.zeros(N * 8, bool); inB[list(B)] = True
    s = pycryptosat.Solver(threads=int(os.environ.get('THREADS', 1)))
    nxt = [N * 8 + 1]; ncons = 0
    for Fl, Vl, routed, IX in ((PF, PV, rp, PIX), (LF, LV, rl, LIX)):
        st_, ids = IX
        cand = np.unique(np.concatenate([ids[st_[f]:st_[f + 1]] for f in B]))
        cand = cand[~routed[cand]]
        Fc = Fl[cand]; Vc = Vl[cand]; fb = inB[Fc]; hasb = fb.any(-1)
        cpar = np.where(fb, 0, nu[Fc]).sum(-1) & 1
        constg = Vc & ~hasb
        cmixed = (np.where(constg, cpar, 0).max(1) != np.where(constg, cpar, 1).min(1)) & constg.any(1)
        for kk in np.nonzero(~cmixed)[0]:
            ps = []
            for g in range(8):
                if not Vc[kk, g]: continue
                fr = [int(f) + 1 for f in Fc[kk, g] if inB[f]]
                if fr:
                    v = nxt[0]; nxt[0] += 1; s.add_xor_clause([v] + fr, bool(cpar[kk, g])); ps.append(v)
                else:
                    ps.append(True if cpar[kk, g] else False)
            lits = [p for p in ps if not isinstance(p, bool)]; consts = [p for p in ps if isinstance(p, bool)]
            # not all equal: OR(p) and OR(not p), with constants folded
            assert lits
            if True not in consts: s.add_clause(lits)
            if False not in consts: s.add_clause([-v for v in lits])
            ncons += 1
    # fixed flags are not variables here (folded); ball flags are vars f+1
    t0 = time.time(); sat, sol = s.solve()
    return sat, sol, ncons, time.time() - t0
for K in [int(x) for x in os.environ.get('SIZES', '600 1000 1500 2000 2500 3000').split()]:
    B = ball(K)
    sat, sol, nc, dt = solve_ball(B)
    print('ball', len(B), 'constraints', nc, 'result', sat, '%.1fs' % dt, flush=True)
    if sat:
        for f in B: nu[f] = 1 if sol[f + 1] else 0
        set_unmixed(nu); print('exact after SAT:', total(sig), flush=True); cur = total(sig)[0]; write(sig); break
