# Hub gadget search, filtered by exact BFS in the modified graph G' (hubs z,z' and freed vertices), then apsp.
# Usage: gadget2.py BASE_EDGES N d D TRIALS SEED OUTPREFIX
import sys, random, subprocess
import numpy as np
from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import shortest_path
APSP = "/home/user/degree-diameter/research/d12D8/r2/apsp"
def load(fn):
    with open(fn) as f:
        n = int(f.readline()); E = np.loadtxt(f, dtype=np.int64).reshape(-1, 2)
    return n, E
def build(n, keep_edges, N_hubs_pairs=None):
    rows = []; cols = []
    for a, b in keep_edges:
        rows += [a, b]; cols += [b, a]
    return csr_matrix((np.ones(len(rows), dtype=np.int8), (rows, cols)), shape=(n, n))
def main():
    base, N, d, D, trials, seed, outp = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6]), sys.argv[7]
    rng = random.Random(seed); np.random.seed(seed)
    n, E = load(base)
    A_side = np.arange(n) < N
    adj = [[] for _ in range(n)]
    for a, b in E:
        if a >= N: a, b = b, a
        adj[a].append(int(b)); adj[b].append(int(a))
    R = D - 2
    G0 = build(n, E.tolist())
    def cover(cands, G):
        return shortest_path(G, unweighted=True, directed=False, indices=cands) <= R
    passed = 0
    for t in range(trials):
        pool = rng.sample(list(np.where(~A_side)[0]), 400)
        cov = cover(pool, G0) & (~A_side)[None, :]
        covered = np.zeros(n, bool); bset = []
        for _ in range(d):
            gain = (cov & ~covered[None, :]).sum(axis=1).astype(np.int64)
            for c in bset: gain[pool.index(c)] = -1
            j = int(np.argmax(gain)); bset.append(pool[j]); covered |= cov[j]
        aset = []; used = set(); covA = np.zeros(n, bool)
        for b in bset:
            nb = [x for x in adj[b] if x not in used and A_side[x]]
            if not nb: break
            c = cover(nb, G0) & A_side[None, :]
            gain = (c & ~covA[None, :]).sum(axis=1).astype(np.int64)
            j = int(np.argmax(gain)); aset.append(nb[j]); used.add(nb[j]); covA |= c[j]
        if len(aset) < d: continue
        pairs = list(zip(aset, bset))
        pset = set((min(a, b), max(a, b)) for a, b in pairs)
        keep = [(int(a), int(b)) for a, b in E if (min(a, b), max(a, b)) not in pset]
        z, zp = n, n + 1
        keep += [(z, b) for a, b in pairs] + [(zp, a) for a, b in pairs]
        nn = n + 2
        G1 = build(nn, keep)
        sources = [z, zp] + [a for a, b in pairs] + [b for a, b in pairs]
        dist = shortest_path(G1, unweighted=True, directed=False, indices=sources)
        far = int((dist > D).sum())
        if far == 0:
            passed += 1
            fn = f"{outp}_s{seed}_t{t}.edges.txt"
            with open(fn, "w") as f:
                f.write(f"{nn}\n")
                for a, b in keep: f.write(f"{a} {b}\n")
            r = subprocess.run([APSP, fn, str(d), str(D)], capture_output=True, text=True, timeout=250).stdout.strip().splitlines()
            print("trial", t, "passes local filter; apsp:", r[-2:] if r else r, flush=True)
            if r and r[-1].startswith("RESULT VALID"):
                print("VALID FOUND", fn, pairs, flush=True); return
        else:
            print("trial", t, "far from hub/freed sources:", far, flush=True)
    print("done; local-filter passes:", passed)
main()
