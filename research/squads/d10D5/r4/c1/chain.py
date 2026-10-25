#!/usr/bin/env python3
"""c1 (round 4): ejection-chain neighbourhoods for the exact CP-SAT step lns.lns_step.

route_counts() mirrors lns.cover but lists, for every (flag, side, target), its active routes; each route is the set of
non-freed sigma literals (x, L) it uses.  A hole is covered by a single move (a swap of two sigma values):
  type (i):  x non-freed collinear with p, sigma(x) := M for a line M through the target (partner = sigma^-1(M));
  type (ii): sigma(u) := L2 for a line L2 through z = sigma^-1(w), w a non-freed line through p (partner = sigma^-1(L2)).
The move is scored by the exact cover; the targets it leaves uncovered are the lost last routes.  The chain S is the
move points plus, for every lost target, its dependency pool (preimages of the lines through it, the points collinear
with its flag point, the z's); lns_step solves S exactly; uncovered targets of the result open the next level.
usage: SECS=... STEP=... SIZE=... DEPTH=... TOPK=... SEED=... python3 chain.py IN.sol OUTPREFIX
"""
import sys, os, time, random
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D5/r4')
import numpy as np
import lns
from lns import N, PTS, LOF, PM, LM, cover, lns_step, read_sol, write_sol


def sinv_of(sig):
    s = np.empty(N, np.int64); s[sig] = np.arange(N); return s


def route_counts(F, sig, hubadj):
    """{(i, side, target): [route, ...]} active routes of cover(); route = tuple of literals (x, L) (sig(x) = L)."""
    sinv = sinv_of(sig)
    k = len(F); isfree = np.zeros(N, bool); isfree[F] = True
    isfreeL = np.zeros(N, bool); isfreeL[sig[F]] = True
    R = {}
    def add(key, lits): R.setdefault(key, []).append(tuple(sorted(set(lits))))
    for i, p in enumerate(F):
        opp = ~PM[p]; opp[p] = False
        for x in np.nonzero(PM[p] & ~isfree)[0]:                       # p - L - x - sig(x) - u
            L = int(sig[x])
            for u in PTS[L]:
                if opp[u]: add((i, 0, int(u)), [(int(x), L)])
        for w in LOF[p]:                                               # p - w - z - L2 - u, z = sig^-1(w)
            w = int(w)
            if isfreeL[w]: continue
            z = int(sinv[w])
            for L2 in LOF[z]:
                u = int(sinv[L2])
                if isfree[u] or not opp[u]: continue
                add((i, 0, u), [(z, w), (u, int(L2))])
        for j in range(k):
            if hubadj[i, j]:
                for u in PTS[sig[F[j]]]:
                    if opp[u]: add((i, 0, int(u)), [])
        l = int(sig[p]); oppl = ~LM[l]; oppl[l] = False
        for M in np.nonzero(LM[l] & ~isfreeL)[0]:                      # l - y - M - z - m, z = sig^-1(M)
            z = int(sinv[M])
            for m in LOF[z]:
                if oppl[m]: add((i, 1, int(m)), [(z, int(M))])
        for y in PTS[l]:
            if isfree[y]: continue
            Ly = int(sig[y])
            for z in PTS[Ly]:
                if isfree[z]: continue
                m = int(sig[z])
                if oppl[m]: add((i, 1, m), [(int(y), Ly), (int(z), m)])
        for j in range(k):
            if hubadj[j, i]:
                for m in LOF[F[j]]:
                    if oppl[m]: add((i, 1, int(m)), [])
    return R


def pool(F, sig, isfree, isfreeL, t):
    """dependency pool of target t: (core, ext) point lists (core = preferred, ext = random extras)"""
    i, side, u = t; p = F[i]; sinv = sinv_of(sig)
    if side == 0:
        core = [int(x) for x in sinv[LOF[u]]] + [int(u)] + [int(sinv[w]) for w in LOF[p] if not isfreeL[w]]
        ext = [int(x) for x in np.nonzero(PM[p] & ~isfree)[0]]
    else:
        l = int(sig[p])
        core = [int(y) for y in PTS[u]] + [int(sinv[u])] + [int(y) for y in PTS[l] if not isfree[y]]
        ext = [int(sinv[M]) for M in np.nonzero(LM[l] & ~isfreeL)[0]]
    core = [x for x in dict.fromkeys(core) if not isfree[x]]
    ext = [x for x in dict.fromkeys(ext) if not isfree[x]]
    return core, ext


def moves_for_hole(F, sig, hubadj, hole):
    """all single swaps (type i and type ii) that cover the hole"""
    i, side, u = hole; p = F[i]; sinv = sinv_of(sig)
    k = len(F); isfree = np.zeros(N, bool); isfree[F] = True
    isfreeL = np.zeros(N, bool); isfreeL[sig[F]] = True
    mv = []
    if side == 0:
        for x in np.nonzero(PM[p] & ~isfree)[0]:
            for M in LOF[u]:
                if isfreeL[M]: continue
                y = int(sinv[M])
                if y == x: continue
                mv.append({int(x): int(M), y: int(sig[x])})
        for w in LOF[p]:
            if isfreeL[w]: continue
            z = int(sinv[w])
            for L2 in LOF[z]:
                if isfreeL[L2] or int(L2) == int(sig[u]): continue
                y = int(sinv[L2])
                if y == u or isfree[y]: continue
                mv.append({int(u): int(L2), y: int(sig[u])})
    else:
        l = int(sig[p])
        # dual: sigma(z) := l-side line through a point of PTS[u]  (z on target line m=u, sig(z) concurrent with l)
        for z in PTS[u]:
            if isfree[z]: continue
            for M in np.nonzero(LM[l] & ~isfreeL)[0]:
                if int(M) == int(sig[z]): continue
                y = int(sinv[M])
                if isfree[y]: continue
                mv.append({int(z): int(M), y: int(sig[z])})
    return mv


def chain(F, sig, hubadj, cost0, unc0, hole, mv, rng, size, depth, ntake, log):
    """one ejection chain from the hole state sig with move mv; returns (sig, cost, uncovered)"""
    isfree = np.zeros(N, bool); isfree[F] = True
    base = sig.copy()
    for x, L in mv.items(): base[x] = L
    c_post, U_post = cover(F, base, hubadj, listing=True)
    before = set(unc0)
    lost = [t for t in U_post if t not in before]          # targets whose last route the move kills
    log.append('   move cost %d lost %s' % (c_post, lost[:6]))
    keep = [int(x) for x in mv if not isfree[x]]
    cur, cur_c, cur_u = sig.copy(), cost0, list(unc0)
    pending = [hole] + lost
    expanded = set(); S = list(keep)
    for lev in range(depth + 1):
        pend = [t for t in pending if t not in expanded]; rng.shuffle(pend)
        for t in pend[:ntake]:
            expanded.add(t)
            core, ext = pool(F, cur, isfree, np.isin(np.arange(N), cur[F]), t)
            rng.shuffle(core); rng.shuffle(ext)
            S = list(dict.fromkeys(S + core[:12] + ext[:5]))
        if len(S) > size:
            rest = [x for x in S if x not in keep]; rng.shuffle(rest)
            S = keep + rest[:max(0, size - len(keep))]
        if not S: break
        tb = time.time()
        new, info = lns_step(F, cur, hubadj, S, STEP_SECS, rng.randint(1, 10 ** 6), 1)
        if new is None:
            log.append('   lev %d |S| %d no solution' % (lev, len(S))); break
        c, U = cover(F, new, hubadj, listing=True)
        log.append('   lev %d |S| %d model %s exact %d %.1fs' % (lev, len(S), info, c, time.time() - tb))
        cur, cur_c, cur_u = new, c, U
        if c == 0: break
        pending = [t for t in U]
    return cur, cur_c, cur_u


STEP_SECS = float(os.environ.get('STEP', 15))


def main():
    S0 = read_sol(sys.argv[1]); out = sys.argv[2]
    F = S0['F']; sig = S0['sig'].copy(); hubadj = S0['hubadj']
    total = float(os.environ.get('SECS', 500)); size = int(os.environ.get('SIZE', 90))
    depth = int(os.environ.get('DEPTH', 2)); topk = int(os.environ.get('TOPK', 30))
    ntake = int(os.environ.get('NTAKE', 3)); seed = int(os.environ.get('SEED', 1))
    rng = random.Random(seed)
    cost, unc = cover(F, sig, hubadj, listing=True)
    best = cost
    print('start cost', cost, 'holes', unc[:10], flush=True)
    rc = route_counts(F, sig, hubadj)
    print('route counts: targets with 1 active route', sum(1 for v in rc.values() if len(v) == 1),
          'of', len(rc), flush=True)
    t0 = time.time(); it = 0
    while time.time() - t0 < total and cost > 0:
        it += 1
        hole = unc[rng.randrange(len(unc))]
        mvs = moves_for_hole(F, sig, hubadj, hole)
        scored = []
        for m in mvs:
            s2 = sig.copy()
            for x, L in m.items(): s2[x] = L
            scored.append((cover(F, s2, hubadj), m))
        if not scored:
            print('it', it, 'no moves for hole', hole, flush=True); continue
        scored.sort(key=lambda t: t[0])
        top = scored[:topk]
        c_mv, mv = top[rng.randrange(len(top))]
        print('it %d hole %s moves %d best move cost %d chosen %d' % (it, hole, len(scored), scored[0][0], c_mv), flush=True)
        log = []
        new, c, U = chain(F, sig, hubadj, cost, unc, hole, mv, rng, size, depth, ntake, log)
        for ln in log: print(ln, flush=True)
        acc = c <= cost
        print('  chain result %d %s' % (c, 'ACC' if acc else 'rej'), flush=True)
        if acc:
            sig = new; cost = c; unc = U if U else []
            if cost < best:
                best = cost; write_sol(out + '.sol', S0, sig, cost)
                print('  new best', best, flush=True)
        if cost == 0:
            write_sol(out + '.sol', S0, sig, 0)
            print('COVERAGE 0 reached', flush=True)
            break
    write_sol(out + '.final.sol', S0, sig, cost)
    print('final cost', cost, 'best', best, 'iters', it, flush=True)


if __name__ == '__main__':
    main()
