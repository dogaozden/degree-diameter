#!/usr/bin/env python3
# Card d15 (wildcard, (4,9)): bi-coset graphs C(G,H,K) with |H| = |K| = 4 and H cap K = 1.
# G = metacyclic Z_m x|_r Z_k, order M = 4N. Left vertices G/H, right vertices G/K, and
# gH ~ kK iff they meet. Every x in G gives exactly one edge (xH, xK), so the graph is simple
# and 4-regular with n = 2N = M/2. G acts transitively on each side, so the diameter is
# max(ecc(L0), ecc(R0)) and the cost (as lift's: far vertices from L0 plus from R0) needs 2 BFS.
import sys, time, random
import numpy as np

D = 9

def make_mul(m, k, r):
    rp = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    def mul(x, y):
        ax = x % m; jx = x // m; ay = y % m; jy = y // m
        return (ax + rp[jx] * ay) % m + m * ((jx + jy) % k)
    return mul

def subgroups4(M, mul):
    N = M
    idx = np.arange(N, dtype=np.int64)
    x2 = mul(idx, idx)
    x4 = mul(x2, x2)
    X4 = idx[(x4 == 0) & (x2 != 0)]
    I2 = idx[(x2 == 0) & (idx != 0)]
    subs = set()
    for x in X4.tolist():
        y = int(x2[x]); z = int(mul(np.int64(x), np.int64(y)))
        subs.add(tuple(sorted((0, x, y, z))))
    for a in I2.tolist():
        ab = mul(np.int64(a), I2); ba = mul(I2, np.int64(a))
        ok = np.nonzero((ab == ba) & (ab != 0))[0]
        for t in ok.tolist():
            b = int(I2[t])
            if b > a:
                subs.add(tuple(sorted((0, a, b, int(ab[t])))))
    return sorted(subs)

def coset_ids(N, mul, H):
    xs = np.arange(N, dtype=np.int64)
    reps = np.stack([mul(xs, np.int64(h)) for h in H])
    canon = reps.min(axis=0)
    uniq, inv = np.unique(canon, return_inverse=True)
    return inv.astype(np.int64), len(uniq)

def build_nbr(N, mul, H, K):
    idH, NL = coset_ids(N, mul, H)
    idK, NR = coset_ids(N, mul, K)
    oH = np.argsort(idH, kind='stable')
    left = idK[oH].reshape(NL, 4) + NL
    oK = np.argsort(idK, kind='stable')
    right = idH[oK].reshape(NR, 4)
    return np.vstack([left, right]).astype(np.int64), idH, idK, NL

def bfs(nbr, s):
    V = nbr.shape[0]
    dist = np.full(V, -1, np.int32)
    dist[s] = 0
    fr = np.array([s], dtype=np.int64)
    d = 0
    while fr.size:
        d += 1
        nx = np.unique(nbr[fr].ravel())
        nx = nx[dist[nx] < 0]
        if nx.size == 0:
            break
        dist[nx] = d
        fr = nx
    return dist

def cost_of(nbr, NL):
    tot = 0
    for s in (0, NL):
        dist = bfs(nbr, s)
        tot += int(np.sum((dist < 0) | (dist > D)))
    return tot

def write_edges(path, nbr, NL):
    V = nbr.shape[0]
    with open(path, 'w') as f:
        f.write(f"{V}\n")
        for i in range(NL):
            for j in nbr[i]:
                f.write(f"{i} {int(j)}\n")

def main():
    Mlo, Mhi, samples, tlimit, seed, tag = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4]), int(sys.argv[5]), sys.argv[6]
    rng = random.Random(seed)
    t0 = time.time()
    best = None
    results = []
    ngroups = 0; nevals = 0
    stop = False
    for M in range(Mlo, Mhi + 1):
        if M % 4: continue
        for k in range(2, M + 1):
            if M % k: continue
            m = M // k
            if m < 2: continue
            rr = np.arange(1, m, dtype=np.int64)
            # vectorised r^k mod m
            base = rr.copy(); res = np.ones_like(rr); e = k
            while e:
                if e & 1: res = (res * base) % m
                base = (base * base) % m
                e >>= 1
            good = rr[(res == 1 % m)]
            good = [int(r) for r in good if np.gcd(int(r), m) == 1]
            for r in good:
                if time.time() - t0 > tlimit:
                    stop = True; break
                mul = make_mul(m, k, r)
                subs = subgroups4(M, mul)
                ngroups += 1
                if len(subs) < 2: continue
                sets = [set(s) for s in subs]
                tries = 0; done = 0
                while done < samples and tries < 20 * samples:
                    tries += 1
                    a = rng.randrange(len(subs)); b = rng.randrange(len(subs))
                    if a == b or (sets[a] & sets[b]) != {0}: continue
                    H, K = subs[a], subs[b]
                    nbr, idH, idK, NL = build_nbr(M, mul, H, K)
                    c = cost_of(nbr, NL)
                    nevals += 1; done += 1
                    rec = (c, M, m, k, r, H, K)
                    results.append(rec)
                    if best is None or c < best[0]:
                        best = rec
                        print(f"best cost={c} n={2*NL} meta({m},{k},{r}) H={H} K={K} t={time.time()-t0:.1f}s", flush=True)
                        if c == 0:
                            write_edges(f"/home/user/degree-diameter/research/squads/b48/r3/d15/{tag}_valid.edges", nbr, NL)
                    if time.time() - t0 > tlimit:
                        stop = True; break
                if stop: break
            if stop: break
        if stop: break
    results.sort()
    print(f"groups={ngroups} evals={nevals} time={time.time()-t0:.1f}s stopped_early={stop}")
    for rec in results[:8]:
        print("top", rec[0], "n=", 2 * rec[1] // 4 * 2 // 2 * 1 if False else rec[1] // 2, f"meta({rec[2]},{rec[3]},{rec[4]})", rec[5], rec[6])

if __name__ == '__main__':
    main()
