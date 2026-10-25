# Hub gadget (+2 vertices): delete a matching M={(a_i,b_i)} of size d, add hub z (A-side) ~ all b_i and hub z' (B-side) ~ all a_i.
# Usage: gadget.py BASE_EDGES N d D TRIALS SEED OUTPREFIX
import sys, random
import numpy as np
from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import shortest_path

def load(fn):
    with open(fn) as f:
        n = int(f.readline())
        E = np.loadtxt(f, dtype=np.int64).reshape(-1, 2)
    return n, E

def main():
    base, N, d, D, trials, seed, outp = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6]), sys.argv[7]
    rng = random.Random(seed)
    n, E = load(base)
    # orient: A = [0,N), B = [N,2N)
    A_side = np.arange(n) < N
    adj = [[] for _ in range(n)]
    for a, b in E:
        if a >= N:
            a, b = b, a
        adj[a].append(b); adj[b].append(a)
    rows = np.concatenate([E[:, 0], E[:, 1]]); cols = np.concatenate([E[:, 1], E[:, 0]])
    G = csr_matrix((np.ones(len(rows), dtype=np.int8), (rows, cols)), shape=(n, n))
    print("base n", n, "edges", len(E), flush=True)
    # radius-(D-2) same-side coverage used for hub domination: B-side needs d(b,y) <= D-2 ; A-side needs d(a,x) <= D-2
    R = D - 2
    # Candidate pool per side: random sample
    def cover_sets(cands):
        dist = shortest_path(G, unweighted=True, directed=False, indices=cands)
        return dist <= R  # rows: candidates, cols: all vertices
    # greedy domination of one side by d vertices from a pool, returns chosen list and uncovered count
    def greedy(side_mask, pool):
        cov = cover_sets(pool)
        cov = cov & side_mask[None, :]
        target = side_mask.copy()
        chosen = []; covered = np.zeros(n, dtype=bool)
        for _ in range(d):
            gain = (cov & ~covered[None, :]).sum(axis=1).astype(np.int64)
            for c in chosen: gain[pool.index(c)] = -1
            j = int(np.argmax(gain)); chosen.append(pool[j]); covered |= cov[j]
        return chosen, int((side_mask & ~covered).sum())
    best = None
    for t in range(trials):
        poolB = rng.sample(list(np.where(~A_side)[0]), 400)
        bset, uncB = greedy(~A_side, poolB)
        # partners: for each b choose the neighbour a maximising A-coverage greedily, distinct
        ok = True; used = set(); aset = []
        covA = np.zeros(n, dtype=bool)
        for b in bset:
            nbrs = [x for x in adj[b] if x not in used]
            if not nbrs:
                ok = False; break
            cands = nbrs
            cov = cover_sets(cands) & A_side[None, :]
            gain = (cov & ~covA[None, :]).sum(axis=1).astype(np.int64)
            j = int(np.argmax(gain)); a = cands[j]
            aset.append(a); used.add(a); covA |= cov[j]
        uncA = int((A_side & ~covA).sum()) if ok else -1
        print(f"trial {t}: uncovered B {uncB}, uncovered A {uncA}", flush=True)
        if ok and uncB == 0 and uncA == 0:
            pairs = list(zip(aset, bset))
            # write augmented graph
            Ed = [(int(a), int(b)) for a, b in E]
            pset = set((min(a, b), max(a, b)) for a, b in pairs)
            keep = [(int(a), int(b)) for a, b in E if (min(a, b), max(a, b)) not in pset]
            z, zp = n, n + 1
            keep += [(z, b) for a, b in pairs] + [(zp, a) for a, b in pairs]
            fn = f"{outp}_t{t}.edges.txt"
            with open(fn, "w") as f:
                f.write(f"{n+2}\n")
                for a, b in keep:
                    f.write(f"{a} {b}\n")
            print("WROTE", fn, "pairs", pairs, flush=True)
            best = fn
            break
    print("BEST", best)

main()
