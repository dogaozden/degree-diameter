"""ARW-style iterated local search for a large pairwise non-orthogonal set in PG(5,8) (= partial ovoid of Q(6,8)).
Graph G: adjacency = orthogonal (w=0). Independent set in G = our set. tau[v] = #S-neighbours of v."""
import sys, time, random
import numpy as np
from base import *
Pc = [np.ascontiguousarray(P[:, k]) for k in range(6)]
def wrow(u):
    r = MUL[u[0], Pc[3]] ^ MUL[u[3], Pc[0]] ^ MUL[u[1], Pc[4]] ^ MUL[u[4], Pc[1]] ^ MUL[u[2], Pc[5]] ^ MUL[u[5], Pc[2]]
    return r
def orth_mask(i):
    m = wrow(P[i]) == 0
    m[i] = False
    return m
class State:
    def __init__(self):
        self.inS = np.zeros(N, bool); self.tau = np.zeros(N, np.int32); self.S = set()
        self.cache = {}
    def add(self, v):
        self.inS[v] = True; self.S.add(v); self.tau += orth_mask(v)
    def rem(self, v):
        self.inS[v] = False; self.S.discard(v); self.tau -= orth_mask(v)
    def fill_free(self, rng):
        free = np.where((self.tau == 0) & ~self.inS)[0]
        rng.shuffle(free)
        for v in free:
            if self.tau[v] == 0 and not self.inS[v]: self.add(int(v))
    def rebuild(self, Sl):
        self.inS[:] = False; self.tau[:] = 0; self.S = set()
        for v in Sl: self.add(v)
def two_improve(st, rng):
    any_imp = False
    while True:
        T1 = np.where((st.tau == 1) & ~st.inS)[0]
        if len(T1) < 2: break
        PT = P[T1]
        found = False
        order = list(st.S); rng.shuffle(order)
        for x in order:
            ux = P[x]
            r = MUL[ux[0], PT[:, 3]] ^ MUL[ux[3], PT[:, 0]] ^ MUL[ux[1], PT[:, 4]] ^ MUL[ux[4], PT[:, 1]] ^ MUL[ux[2], PT[:, 5]] ^ MUL[ux[5], PT[:, 2]]
            L = T1[r == 0]
            if len(L) < 2: continue
            PL = P[L]
            W = np.zeros((len(L), len(L)), dtype=np.int64)
            for k in range(6): W ^= MUL[PL[:, k][:, None], PL[:, SIG[k]][None, :]]
            iu = np.argwhere(np.triu(W != 0, 1))
            if len(iu) == 0: continue
            a, b = iu[rng.randrange(len(iu))]
            u, v = int(L[a]), int(L[b])
            st.rem(x); st.add(u); st.add(v); st.fill_free(rng)
            found = True; any_imp = True
            break
        if not found: break
    return any_imp
def run(seedset, seed, tlimit, out_prefix, log):
    rng = random.Random(seed)
    st = State()
    st.rebuild(seedset)
    st.fill_free(rng); two_improve(st, rng)
    best = len(st.S); bestS = sorted(st.S)
    log('start size %d' % best)
    t0 = time.time(); it = 0; cur = list(st.S); last_imp = 0
    while time.time() - t0 < tlimit:
        it += 1
        prev = sorted(st.S)
        # perturbation: force-insert a random non-solution vertex (preferring low tightness)
        k = 1 if rng.random() < 0.8 else 2
        for _ in range(k):
            cand = np.where((~st.inS) & (st.tau <= 2))[0]
            if len(cand) == 0: cand = np.where(~st.inS)[0]
            v = int(cand[rng.randrange(len(cand))])
            nb = np.where(wrow(P[v]) == 0)[0]
            for x in nb:
                if st.inS[x]: st.rem(int(x))
            st.add(v)
        st.fill_free(rng)
        two_improve(st, rng)
        sz = len(st.S)
        if sz > best:
            best = sz; bestS = sorted(st.S); last_imp = it
            fn = '%s_%d.txt' % (out_prefix, best)
            open(fn, 'w').write(' '.join(map(str, bestS)) + '\n')
            log('it %d time %.0f new best %d' % (it, time.time() - t0, best))
        if sz < len(prev) - 1 or (sz < len(prev) and rng.random() < 0.7):
            st.rebuild(prev)   # revert
        if it - last_imp > 3000:
            st.rebuild(bestS); last_imp = it
    log('done it %d best %d' % (it, best))
    return best, bestS
if __name__ == '__main__':
    mode, seed, tl = sys.argv[1], int(sys.argv[2]), float(sys.argv[3])
    logf = open('/home/user/degree-diameter/research/squads/hexfam_r1/c7/ils_%s_%d.log' % (mode, seed), 'w')
    def log(s):
        logf.write(s + '\n'); logf.flush()
    if mode == 'start217':
        seedset = load_set('/home/user/degree-diameter/research/d10D7/sets/P8_r5c4_217.txt')
    else:
        seedset = []
    run(seedset, seed, tl, '/home/user/degree-diameter/research/squads/hexfam_r1/c7/ils_%s_%d' % (mode, seed), log)
