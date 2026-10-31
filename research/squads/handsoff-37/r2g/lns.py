# r2g: orbit-level LNS for G-invariant cubic bipartite graphs. Destroy k chosen edge orbits, re-complete
# with a randomised exact DFS (first completion found), accept by Metropolis on far. Calibrated on a fixed composition.
import sys, os, time, random, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import orb
from orb import *
from run import group_def

class Comp:
    def __init__(self, S, sideA, sideB):
        nA, nB = len(sideA), len(sideB)
        offA = []; o = 0
        for c in sideA: offA.append(o); o += S.sizes[c]
        offB = []; o2 = 0
        for c in sideB: offB.append(o2); o2 += S.sizes[c]
        assert o == o2
        self.m = m = o
        self.nA = nA; self.nB = nB
        edges = []
        inc = [[] for _ in range(nA+nB)]
        for i, ca in enumerate(sideA):
            for j, cb in enumerate(sideB):
                for pairs, dX, dY in S.eo(ca, cb):
                    eid = len(edges)
                    gp = [(offA[i]+p, m+offB[j]+q) for (p, q) in pairs]
                    edges.append((i, nA+j, dX, dY, gp))
                    inc[i].append(eid); inc[nA+j].append(eid)
        self.edges = edges; self.inc = inc; self.E = len(edges)
        self.feasible = all(len(inc[v]) > 0 for v in range(nA+nB))

    def complete(self, forced, rng):
        """randomised DFS: returns a list of chosen edge ids (completion containing forced) or None"""
        edges, inc, nA = self.edges, self.inc, self.nA
        V = self.nA + self.nB
        status = [0]*self.E
        res = [3]*V
        for e in forced:
            status[e] = 1
            res[edges[e][0]] -= edges[e][2]; res[edges[e][1]] -= edges[e][3]
        if min(res) < 0: return None
        out = [None]
        budget = [20000]
        def other(e, v):
            return edges[e][1] if edges[e][0] == v else edges[e][0]
        def dfs():
            budget[0] -= 1
            if budget[0] < 0 or out[0] is not None: return
            bv = None; bc = None
            for v in range(V):
                if res[v] > 0:
                    cand = [e for e in inc[v] if status[e] == 0 and (edges[e][2] if v < nA else edges[e][3]) <= res[v]
                            and (edges[e][3] if v < nA else edges[e][2]) <= res[other(e, v)]]
                    if not cand: return
                    if bc is None or len(cand) < len(bc):
                        bv, bc = v, cand
            if bc is None:
                out[0] = [e for e in range(self.E) if status[e] == 1]
                return
            rng.shuffle(bc)
            for t, e in enumerate(bc):
                for x in bc[:t]: status[x] = 2
                status[e] = 1
                ea, eb = edges[e][0], edges[e][1]
                res[ea] -= edges[e][2]; res[eb] -= edges[e][3]
                dfs()
                res[ea] += edges[e][2]; res[eb] += edges[e][3]
                status[e] = 0
                for x in bc[:t]: status[x] = 0
                if out[0] is not None: return
        dfs()
        return out[0]

    def graph(self, chosen):
        n = 2*self.m
        adj = [[] for _ in range(n)]
        ev = []
        for e in chosen:
            ev.extend(self.edges[e][4])
        for (a, b) in ev:
            adj[a].append(b); adj[b].append(a)
        return n, adj, ev

def lns(comp, rng, iters, T0, T1, deadline, kmax=3, log=None):
    chosen = comp.complete([], rng)
    if chosen is None: return None
    n, adj, ev = comp.graph(chosen); cur = far_count(n, adj)
    best = (cur, list(ev))
    t0 = time.time()
    acc = 0; tries = 0; fails = 0
    for it in range(iters):
        if time.time() > deadline: break
        T = T0 * (T1/T0) ** (it/max(1, iters-1))
        k = rng.randint(1, kmax)
        rem = set(rng.sample(chosen, min(k, len(chosen))))
        forced = [e for e in chosen if e not in rem]
        newc = comp.complete(forced, rng)
        tries += 1
        if newc is None:
            fails += 1; continue
        n, adj, ev = comp.graph(newc)
        f = far_count(n, adj)
        d = f - cur
        if d <= 0 or rng.random() < math.exp(-d / T):
            chosen = newc; cur = f; acc += 1
            if f < best[0]:
                best = (f, list(ev))
                if log: log(best[0], it)
    return best, acc, tries, fails

if __name__ == '__main__':
    name = sys.argv[1]; m = int(sys.argv[2]); seconds = float(sys.argv[3])
    comps_spec = sys.argv[4]    # e.g. "0,0,1,1|2,3" class ids; sideA|sideB
    seed = int(sys.argv[5]) if len(sys.argv) > 5 else 1
    T0 = float(os.environ.get('T0', '4')); T1 = float(os.environ.get('T1', '0.5'))
    G = group_from_gens(group_def(name))
    subs = all_subgroups(G); classes = conj_classes(G, subs.keys())
    S = Setup(G, classes)
    rng = random.Random(seed)
    orb.RNG = rng
    A, B = comps_spec.split('|')
    A = [int(x) for x in A.split(',')]; B = [int(x) for x in B.split(',')]
    comp = Comp(S, A, B)
    print('m', comp.m, 'edge orbits', comp.E, 'feasible', comp.feasible, flush=True)
    if not comp.feasible: sys.exit()
    deadline = time.time() + seconds
    res = lns(comp, rng, 10**9, T0, T1, deadline, kmax=int(os.environ.get('KMAX', '3')),
              log=lambda f, it: print('  new best', f, 'it', it, flush=True))
    if res is None:
        print('no completion'); sys.exit()
    (bf, bev), acc, tries, fails = res
    print('RESULT best_far', bf, 'accepted', acc, 'tries', tries, 'failed_completions', fails, flush=True)
    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'out', 'lns_%s_m%d_s%d.edges' % (name, m, seed)), 'w') as fh:
        fh.write('%d\n' % (2*m))
        for (x, y) in bev: fh.write('%d %d\n' % (x, y))
