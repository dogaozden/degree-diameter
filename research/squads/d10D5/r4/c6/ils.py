#!/usr/bin/env python3
"""c6: iterated local search with exact (CP-SAT) repair for the 1-hole 10-flag states of r4.

kick: 3-12 random sigma swaps between non-freed points (biased to hole-relevant points);
repair: lns.lns_step on S = kicked points + neighbourhood of the holes, then FOL more lns_step calls on
neighbourhoods of the remaining holes (greedy within the chain); accept by exact lns.cover with a
Metropolis rule at temperature TEMP.  Logs every iteration.
usage: ils.py SRC.sol OUTPREFIX   env: BUDGET (s), SEED, TEMP, STEP (s per CP-SAT call), FOL, SIZE
"""
import sys, os, time, random, math
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D5/r4')
import numpy as np
import lns
from lns import N, PTS, LOF, read_sol, write_sol, cover, lns_step, neighbourhood


def main():
    src, out = sys.argv[1], sys.argv[2]
    budget = float(os.environ.get('BUDGET', 1100))
    seed = int(os.environ.get('SEED', 1))
    TEMP = float(os.environ.get('TEMP', 0.5))
    STEP = float(os.environ.get('STEP', 4))
    FOL = int(os.environ.get('FOL', 4))
    SIZE = int(os.environ.get('SIZE', 30))
    rng = random.Random(seed)
    S0 = read_sol(src)
    F = S0['F']; H = S0['hubadj']; k = len(F)
    isfree = np.zeros(N, bool); isfree[F] = True
    nonfree = np.nonzero(~isfree)[0]
    cur_sig = S0['sig'].copy()
    cur, unc = cover(F, cur_sig, H, listing=True)
    best, best_sig = cur, cur_sig.copy()
    print('start', src, 'cost', cur, 'holes', unc[:6], 'k', k, 'seed', seed, 'TEMP', TEMP, 'STEP', STEP, flush=True)
    t0 = time.time(); it = 0; acc_n = 0
    while cur > 0 and time.time() - t0 < budget:
        it += 1
        tb = time.time()
        sig = cur_sig.copy()
        sinv = np.empty(N, np.int64); sinv[sig] = np.arange(N)
        # ---- hole-relevant points (mirrors lns.neighbourhood)
        rel = set()
        for (i, side, t) in unc:
            p = F[i]
            if side == 0:
                rel.update(np.nonzero(lns.PM[p] & ~isfree)[0].tolist())
                rel.update(sinv[LOF[t]].tolist()); rel.add(int(t))
                rel.update(sinv[LOF[p]].tolist())
            else:
                l = int(sig[p])
                rel.update(sinv[np.nonzero(lns.LM[l])[0]].tolist())
                rel.update(PTS[t].tolist()); rel.add(int(sinv[t]))
        rel = [int(x) for x in rel if not isfree[x]]
        # ---- kick: 1-3 swaps (occasionally 4-8), endpoints biased to hole-relevant points; resample until the
        # kicked cost lies in [1, 40] (single random swaps cost ~20 each on this state, so 3-12 random swaps are too strong)
        for _try in range(30):
            sig = cur_sig.copy()
            nsw = rng.randint(1, 3) if rng.random() < 0.75 else rng.randint(4, 8)
            touched = []
            for _ in range(nsw):
                x = rng.choice(rel) if (rel and rng.random() < 0.6) else int(rng.choice(nonfree))
                y = rng.choice(rel) if (rel and rng.random() < 0.5) else int(rng.choice(nonfree))
                if x == y: continue
                sig[x], sig[y] = sig[y], sig[x]
                touched += [x, y]
            touched = list(dict.fromkeys(touched))
            ck0 = cover(F, sig, H)
            if 1 <= ck0 <= 40: break
        c = ck0; ck = c
        # ---- repair chain: CP-SAT on small neighbourhoods (|S| ~ 15-40 solves to optimality in ~0.1 s on this state;
        # |S| = 60-90 with a kick does not even find the undo in 15 s)
        for r in range(1 + FOL):
            if c == 0: break
            _, unc_c = cover(F, sig, H, listing=True)
            sz = rng.randint(SIZE // 2, SIZE + SIZE // 3) if rng.random() < 0.75 else rng.randint(50, 70)
            if r == 0:
                pick = rng.sample(rel, min(len(rel), sz // 2)) if rel else []
                S = list(dict.fromkeys(touched + pick + neighbourhood(F, sig, unc_c, sz - len(touched) - len(pick), rng)))
            else:
                S = neighbourhood(F, sig, unc_c, sz, rng)
            new, info = lns_step(F, sig, H, S, STEP, rng.randint(1, 10 ** 6), 1)
            if new is None:
                continue
            c2, u2 = cover(F, new, H, listing=True)
            if c2 <= c:
                sig, c = new, c2
            if os.environ.get('VERB'): print('    step', r, '|S|', len(S), info, 'exact', c2, flush=True)
        # ---- accept
        if c <= cur or rng.random() < math.exp(-(c - cur) / TEMP):
            cur_sig, cur = sig.copy(), c; acc_n += 1; acc = 'ACC'
        else:
            acc = 'rej'
        if cur < best:
            best, best_sig = cur, cur_sig.copy()
            write_sol(out + '_best.sol', S0, best_sig, best)
            print('  new best', best, flush=True)
        ham = int((cur_sig != S0['sig']).sum())
        print('it %3d nsw %2d |S| %3d kick %3d chain %3d cur %d best %d %s hamming %d %.1fs elapsed %.0fs' %
              (it, nsw, len(S), ck, c, cur, best, acc, ham, time.time() - tb, time.time() - t0), flush=True)
    print('done it', it, 'accepted', acc_n, 'best', best, 'cur', cur, 'elapsed %.0fs' % (time.time() - t0), flush=True)
    write_sol(out + '_final.sol', S0, cur_sig, cur)
    if best == 0:
        print('COVERAGE 0 reached', flush=True)


if __name__ == '__main__':
    main()
