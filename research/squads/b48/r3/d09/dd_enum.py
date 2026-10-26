# d09: enumerate direct and semidirect products in N = 2486..2900, cheap invariants, numpy proxy for Haar cover.
# Proxy: for S = {e,a,b,c} (e in S), W_t = products of <= t elements of S. Haar cost (D=9) = (N-|W_8|) + (N-|W_9|)
# (side A needs W_8 = G, side B needs W_9 = G), so maximizing |W_8|+|W_9| is the haar objective. Hill climb in numpy.
import sys, os, random, json, time
import numpy as np
T_DIR = "/home/user/degree-diameter/research/squads/b48/tools"
sys.path.insert(0, T_DIR)
import groups

LO, HI = 2486, 2900
OUT = "/home/user/degree-diameter/research/squads/b48/r3/d09"

def invariants(T):
    N = len(T)
    idx = np.arange(N)
    # element orders
    order = np.zeros(N, dtype=np.int64)
    pw = idx.copy(); k = 1
    done = pw == 0
    order[done] = 1
    while not done.all() and k < 10000:
        pw = T[pw, idx].astype(np.int64); k += 1
        newly = (pw == 0) & (order == 0)
        order[newly] = k
        done = order > 0
    hist = {}
    for o in order.tolist():
        hist[o] = hist.get(o, 0) + 1
    # centre
    cen = int(np.sum(np.all(T == T.T, axis=1)))
    return hist, cen

def sig(hist, cen, N):
    return (N, cen, tuple(sorted(hist.items())))

def proxy(T, rng, iters=150):
    N = len(T)
    def W(S):
        Sa = np.array(S)
        seen = np.zeros(N, bool); seen[0] = True
        cur = np.array([0])
        sizes = [1]
        for t in range(1, 10):
            new = T[Sa][:, cur].ravel().astype(np.int64)
            seen[new] = True
            sizes.append(int(seen.sum()))
            cur = np.nonzero(seen)[0]
        return sizes[8] + sizes[9]  # |W_8| + |W_9|
    best = None
    for rest in range(2):
        S = [0] + rng.sample(range(1, N), 3)
        val = W(S)
        for it in range(iters):
            S2 = list(S)
            j = rng.randrange(1, 4)
            c = rng.randrange(1, N)
            if c in S2: continue
            S2[j] = c
            v2 = W(S2)
            if v2 >= val:
                S, val = S2, v2
        if best is None or val > best[0]:
            best = (val, S)
        if best[0] == 2 * N:
            break
    return best, 2 * N - best[0]

def main():
    specs = json.load(open(sys.argv[1]))[int(sys.argv[2]):int(sys.argv[3])]  # list of [spec, N]
    outname = sys.argv[4]
    rng = random.Random(12345)
    res = []
    seen_sig = {}
    t0 = time.time()
    for spec, N in specs:
        try:
            T = groups.table(spec)
        except Exception as e:
            print("ERR", spec, e, flush=True); continue
        assert len(T) == N, (spec, len(T), N)
        hist, cen = invariants(T)
        s = sig(hist, cen, N)
        if s in seen_sig:
            print("DUP", spec, "=", seen_sig[s], flush=True); continue
        seen_sig[s] = spec
        best, deficit = proxy(T, rng)
        inv = hist.get(2, 0)
        res.append({"spec": spec, "N": N, "deficit": deficit, "S": best[1], "invol": inv, "centre": cen})
        print(f"{spec:55s} N={N} invol={inv} centre={cen} proxy_deficit={deficit}", flush=True)
        if time.time() - t0 > 100: print("time cap"); break
    res.sort(key=lambda r: (r["deficit"], r["invol"]))
    with open(os.path.join(OUT, outname), "w") as f:
        for r in res: f.write(json.dumps(r) + "\n")
    print("done", len(res), time.time() - t0)

if __name__ == "__main__":
    main()
