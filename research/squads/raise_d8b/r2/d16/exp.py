#!/usr/bin/env python3
# d16 wildcard: small-scale test of Haar graphs H(Z_n, S) with a coset-union S = T + {0, n/2}
# versus generic S. Diameter-8 condition for H(G,S) with abelian G:
#   A-side covered:  4D = G,   D = S - S
#   B-side covered:  S + 3D = G
# cost = #uncovered A + #uncovered B (0 means diameter <= 8 for the bipartite Haar graph).
# Plain hill climbing (accept moves with cost <= current), fixed evaluation budget per run.
import sys, time, json
import numpy as np

D8 = 8
def cost(S, n):
    Sind = np.zeros(n); Sind[list(S)] = 1.0
    Dm = np.zeros(n)
    Sl = list(S)
    for s in Sl:
        for t in Sl:
            Dm[(s - t) % n] = 1.0
    fD = np.fft.rfft(Dm)
    K = np.zeros(n); K[0] = 1.0
    K3 = None
    for step in range(4):
        if step == 3:
            K3 = K.copy()
        K = (np.fft.irfft(np.fft.rfft(K) * fD, n) > 0.5).astype(float)
    B = (np.fft.irfft(np.fft.rfft(Sind) * np.fft.rfft(K3), n) > 0.5)
    return int(n - K.sum()) + int(n - B.sum())

def run(family, n, d, E, seed, tlimit):
    rng = np.random.default_rng(seed)
    h = n // 2
    t0 = time.time()
    if family == "generic":
        S = set(rng.choice(n, size=d, replace=False).tolist())
        def move(S):
            S = set(S)
            out = rng.choice(sorted(S))
            while True:
                x = int(rng.integers(n))
                if x not in S:
                    break
            S.remove(int(out)); S.add(x)
            return S
    elif family == "coset":
        m = d // 2
        T = set()
        while len(T) < m:
            x = int(rng.integers(n))
            if x % h not in {y % h for y in T}:
                T.add(x)
        S = set(T) | {(t + h) % n for t in T}
        def move(S):
            Tl = sorted({s % h for s in S})
            out = Tl[int(rng.integers(len(Tl)))]
            rest = [y for y in Tl if y != out]
            while True:
                x = int(rng.integers(h))
                if x not in rest:
                    break
            newT = rest + [x]
            return set(newT) | {(t + h) % n for t in newT}
    c = cost(S, n)
    best = c; evals = 1; hit = None
    while evals < E and c > 0 and time.time() - t0 < tlimit:
        S2 = move(S)
        if len(S2) != d:
            continue
        c2 = cost(S2, n); evals += 1
        if c2 <= c:
            S, c = S2, c2
            if c < best:
                best = c
    return {"family": family, "n": n, "d": d, "seed": seed, "best": best,
            "final": c, "evals": evals, "solved": c == 0, "S": sorted(S) if c == 0 else None,
            "secs": round(time.time() - t0, 1)}

if __name__ == "__main__":
    d = int(sys.argv[1]); E = int(sys.argv[2]); tlimit = float(sys.argv[3])
    ns = [int(x) for x in sys.argv[4].split(",")]
    seeds = int(sys.argv[5])
    fams = sys.argv[6].split(",")
    out = open(sys.argv[7], "a")
    for n in ns:
        for fam in fams:
            if fam == "coset" and n % 2:
                continue
            for seed in range(seeds):
                r = run(fam, n, d, E, seed, tlimit)
                out.write(json.dumps(r) + "\n"); out.flush()
                print(fam, n, seed, "best", r["best"], "evals", r["evals"], "solved", r["solved"], "secs", r["secs"], flush=True)
