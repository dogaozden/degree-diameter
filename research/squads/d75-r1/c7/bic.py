# bic.py: bi-coset graphs B(G;H,K;D) with |H| = |K| = 3 and degree 7 (|D| = 21), N = 2|G|/3 vertices.
# Vertices: H-cosets Hx (ids 0..m-1) and K-cosets Ky (ids m..2m-1), m = |G|/3.  Hx ~ Ky iff y x^-1 in D,
# where D is a union of double cosets K g H (so D K = D, D H = D).  G acts transitively on each side, so
# diameter <= 5 iff BFS from one H-coset and from one K-coset reach everything within 5 steps.
# usage: python3 bic.py FILE.ht SECS SEED [EDGES_OUT]     (prints BEST lines; writes EDGES_OUT on cost 0)
import sys, random, time
import numpy as np

def load(path):
    with open(path) as f:
        n, ninv = map(int, f.readline().split())
        M = np.empty((n, n), dtype=np.int32)
        for i in range(n):
            M[i] = np.array(f.readline().split(), dtype=np.int32)
        inv = np.array(f.readline().split(), dtype=np.int32)
    return n, M, inv

def order3_subgroups(n, M):
    out = {}
    for g in range(1, n):
        g2 = int(M[g, g])
        if g2 != 0 and int(M[g2, g]) == 0:
            out[min(g, g2)] = (0, min(g, g2), max(g, g2))
    return list(out.values())

def cosets(n, M, S, left):
    # left=False: right cosets S x (index c for each x); left=True: left cosets x S
    idx = -np.ones(n, dtype=np.int32); reps = []
    for x in range(n):
        if idx[x] < 0:
            c = len(reps); reps.append(x)
            if left:
                for s in S: idx[M[x, s]] = c
            else:
                for s in S: idx[M[s, x]] = c
    return idx, np.array(reps, dtype=np.int32)

class Bic:
    def __init__(self, path):
        self.n, self.M, self.inv = load(path)
        self.subs = order3_subgroups(self.n, self.M)
    def setup(self, H, K):
        n, M, inv = self.n, self.M, self.inv
        self.H, self.K = H, K
        self.hc, self.rH = cosets(n, M, H, False)   # H x
        self.kc, self.rK = cosets(n, M, K, False)   # K y
        self.m = len(self.rH)
        # left K-cosets K d (for D's K-side reps) and right H-cosets d H (for D's H-side reps)
        self.kl, _ = cosets(n, M, K, False)         # K d  : index by element d
        self.hr, _ = cosets(n, M, H, True)          # d H  : index by element d
        # double cosets K g H
        dl = -np.ones(n, dtype=np.int32); labels = []
        for g in range(n):
            if dl[g] < 0:
                els = set()
                for k in K:
                    kg = M[k, g]
                    for h in H: els.add(int(M[kg, h]))
                lab = len(labels)
                for e in els: dl[e] = lab
                labels.append(sorted(els))
        self.dl = dl; self.labels = labels
        self.big = [i for i, L in enumerate(labels) if len(L) == 9]
        self.small = [i for i, L in enumerate(labels) if len(L) == 3]
        self.nb = []

    def graph(self, chosen):
        # chosen: list of label ids; returns adjacency lists (H-side ids 0..m-1, K-side m..2m-1)
        n, M, m = self.n, self.M, self.m
        D = [e for lab in chosen for e in self.labels[lab]]
        Dl = {}
        for d in D: Dl.setdefault(int(self.kl[d]), d)     # one d per left K-coset
        Dr = {}
        for d in D: Dr.setdefault(int(self.hr[d]), d)     # one d per right H-coset
        Dl = np.array(list(Dl.values()), dtype=np.int32)
        Dr = np.array(list(Dr.values()), dtype=np.int32)
        invDr = self.inv[Dr]
        aH = self.kc[M[Dl][:, self.rH]].T      # (m, 7): K-cosets adjacent to H-coset c
        aK = self.hc[M[invDr][:, self.rK]].T   # (m, 7): H-cosets adjacent to K-coset c'
        return aH, aK

    def cost(self, chosen, bound=5):
        aH, aK = self.graph(chosen)
        m = self.m
        adj = [None] * (2 * m)
        aHl = aH.tolist(); aKl = aK.tolist()
        for c in range(m):
            adj[c] = [m + y for y in aHl[c]]
        for c in range(m):
            adj[m + c] = aKl[c]
        tot = 0
        for root in (int(self.hc[0]), m + int(self.kc[0])):
            seen = bytearray(2 * m); seen[root] = 1
            frontier = [root]; reached = 1
            for _ in range(bound):
                nxt = []
                for u in frontier:
                    for v in adj[u]:
                        if not seen[v]:
                            seen[v] = 1; nxt.append(v)
                reached += len(nxt); frontier = nxt
                if not frontier: break
            tot += 2 * m - reached
        return tot, adj

def edges_of(adj, path):
    N = len(adj)
    with open(path, 'w') as f:
        es = [(u, v) for u in range(N) for v in adj[u] if u < v]
        f.write(f"{N}\n")
        for u, v in es: f.write(f"{u} {v}\n")

def main():
    path = sys.argv[1]; secs = float(sys.argv[2]); seed = int(sys.argv[3])
    out = sys.argv[4] if len(sys.argv) > 4 else None
    rng = random.Random(seed)
    B = Bic(path)
    n = B.n
    subs = B.subs
    if not subs:
        print("NOSUB3"); return
    t0 = time.time(); best_all = None; evals = 0
    while time.time() - t0 < secs:
        H = rng.choice(subs); K = rng.choice(subs)
        B.setup(H, K)
        # random start: composition (2 big,1 small), (1 big,4 small) or (0,7)
        comp = rng.choice([(2, 1), (1, 4), (0, 7)])
        nb, ns = comp
        if nb > len(B.big) or ns > len(B.small): continue
        state_b = rng.sample(B.big, nb); state_s = rng.sample(B.small, ns)
        cur, _ = B.cost(state_b + state_s); evals += 1
        bestc = cur; T = 2.0
        for it in range(400):
            if cur == 0: break
            nb_ = list(state_b); ns_ = list(state_s)
            if nb and rng.random() < 0.5 and len(B.big) > nb:
                i = rng.randrange(nb); cand = rng.choice(B.big)
                if cand in nb_: continue
                nb_[i] = cand
            elif ns and len(B.small) > ns:
                i = rng.randrange(ns); cand = rng.choice(B.small)
                if cand in ns_: continue
                ns_[i] = cand
            else:
                continue
            c2, _ = B.cost(nb_ + ns_); evals += 1
            if c2 <= cur or rng.random() < np.exp(-(c2 - cur) / T):
                state_b, state_s, cur = nb_, ns_, c2
                bestc = min(bestc, cur)
            T = max(0.05, T * 0.98)
            if time.time() - t0 > secs: break
        if best_all is None or bestc < best_all[0]:
            best_all = (bestc, H, K, comp)
        if bestc == 0:
            c0, adj = B.cost(state_b + state_s)
            print("VALID", 2 * B.m, "H", H, "K", K, "comp", comp, flush=True)
            if out: edges_of(adj, out)
            break
    print("BEST", best_all[0] if best_all else None, "N", 2 * B.m, "evals", evals,
          "secs", round(time.time() - t0, 1), flush=True)

if __name__ == "__main__":
    main()
