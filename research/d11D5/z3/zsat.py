"""Exact SAT search for a Z_a covering cocycle on W(q) (see zcov.c): every opposite point pair and every opposite
line pair sees all a values on its q+1 geodesics.  Gauge: flags of a BFS spanning tree are fixed to 0.
usage: python3 zsat.py q a [onlypts] [timeout_s] [out]"""
import sys, struct, time, itertools
from collections import deque
from pysat.solvers import Cadical153
from pysat.card import CardEnc

def load(q):
    b = open(f"gq/gq_q{q}.bin", "rb").read()
    _, N, L = struct.unpack("3i", b[:12])
    Q1 = q + 1
    pl = list(struct.unpack(f"{L*Q1}i", b[12:12 + 4 * L * Q1]))
    lines = [pl[l * Q1:(l + 1) * Q1] for l in range(L)]
    return N, L, lines

def main():
    q, a = int(sys.argv[1]), int(sys.argv[2])
    onlypts = len(sys.argv) > 3 and sys.argv[3] == "1"
    tmo = float(sys.argv[4]) if len(sys.argv) > 4 else 600
    out = sys.argv[5] if len(sys.argv) > 5 else None
    N, L, lines = load(q)
    Q1 = q + 1
    fid = {}
    for l in range(L):
        for k, p in enumerate(lines[l]):
            fid[(p, l)] = l * Q1 + k
    F = L * Q1
    lp = [[] for _ in range(N)]
    for l in range(L):
        for p in lines[l]:
            lp[p].append(l)
    col = {}
    for l in range(L):
        for x in lines[l]:
            for y in lines[l]:
                if x != y:
                    col[(x, y)] = l
    conc = {}
    for p in range(N):
        for x in lp[p]:
            for y in lp[p]:
                if x != y:
                    conc[(x, y)] = p
    nv = [0]
    def new(n):
        r = list(range(nv[0] + 1, nv[0] + 1 + n)); nv[0] += n; return r
    X = [new(a) for _ in range(F)]
    cl = []
    for f in range(F):
        enc = CardEnc.equals(lits=X[f], bound=1, top_id=nv[0]); nv[0] = max(nv[0], enc.nv); cl += enc.clauses
    # gauge: BFS tree on incidence graph
    seen = {("p", 0)}; dq = deque([("p", 0)]); tree = []
    while dq:
        t, x = dq.popleft()
        nb = [("l", l) for l in lp[x]] if t == "p" else [("p", p) for p in lines[x]]
        for y in nb:
            if y not in seen:
                seen.add(y); dq.append(y)
                f = fid[(x, y[1])] if t == "p" else fid[(y[1], x)]
                tree.append(f)
    for f in tree:
        cl.append([X[f][0]])
    # 2-path variables: A[(P,l,R)] = nu(P,l) - nu(R,l);  B[(l,P,k)] = nu(P,k) - nu(P,l)
    A = {}
    def apath(P, l, R):
        key = (P, l, R)
        if key in A: return A[key]
        v = new(a); A[key] = v
        enc = CardEnc.equals(lits=v, bound=1, top_id=nv[0]); nv[0] = max(nv[0], enc.nv); cl.extend(enc.clauses)
        f1, f2 = fid[(P, l)], fid[(R, l)]
        for u in range(a):
            for w in range(a):
                cl.append([-X[f1][u], -X[f2][w], v[(u - w) % a]])
        return v
    def bpath(l, P, k):
        key = ("b", l, P, k)
        if key in A: return A[key]
        v = new(a); A[key] = v
        enc = CardEnc.equals(lits=v, bound=1, top_id=nv[0]); nv[0] = max(nv[0], enc.nv); cl.extend(enc.clauses)
        f1, f2 = fid[(P, k)], fid[(P, l)]
        for u in range(a):
            for w in range(a):
                cl.append([-X[f1][u], -X[f2][w], v[(u - w) % a]])
        return v
    npairs = 0
    def cover(geos):
        # geos: list of (v1, v2) one-hot vectors; need for each z some geodesic with v1 + v2 = z
        for z in range(a):
            ys = new(len(geos))
            cl.append(ys[:])
            for y, (v1, v2) in zip(ys, geos):
                for u in range(a):
                    cl.append([-y, -v1[u], v2[(z - u) % a]])
    for P in range(N):
        for Q in range(P + 1, N):
            if (P, Q) in col: continue
            geos = []
            for l1 in lp[P]:
                R = next(r for r in lines[l1] if r != P and (r, Q) in col)
                l2 = col[(R, Q)]
                geos.append((apath(P, l1, R), apath(R, l2, Q)))
            cover(geos); npairs += 1
    if not onlypts:
        for l in range(L):
            for m in range(l + 1, L):
                if (l, m) in conc: continue
                geos = []
                for P1 in lines[l]:
                    k = next(kk for kk in lp[P1] if kk != l and (kk, m) in conc)
                    P2 = conc[(k, m)]
                    geos.append((bpath(l, P1, k), bpath(k, P2, m)))
                cover(geos); npairs += 1
    print(f"W({q}) a={a} pairs={npairs} vars={nv[0]} clauses={len(cl)}", flush=True)
    s = Cadical153(bootstrap_with=cl)
    t0 = time.time()
    import threading
    timer = threading.Timer(tmo, lambda: s.interrupt()); timer.start()
    r = s.solve_limited(expect_interrupt=True)
    timer.cancel()
    print(f"result={r} time={time.time()-t0:.1f}s", flush=True)
    if r:
        m = set(l for l in s.get_model() if l > 0)
        nu = [next(u for u in range(a) if X[f][u] in m) for f in range(F)]
        if out:
            open(out, "w").write("\n".join(map(str, nu)) + "\n")
            print("wrote", out)

main()
