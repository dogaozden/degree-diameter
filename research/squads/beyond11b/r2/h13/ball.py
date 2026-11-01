# h13: same-side ball growth and uncovered-by-type for random Haar S (Delta=4) on several groups.
import sys, math, random
import numpy as np

def is_prime(n):
    if n < 2: return False
    i = 2
    while i * i <= n:
        if n % i == 0: return False
        i += 1
    return True

def prim_root(p):
    fac = []; m = p - 1; q = 2
    while q * q <= m:
        if m % q == 0:
            fac.append(q)
            while m % q == 0: m //= q
        q += 1
    if m > 1: fac.append(m)
    for g in range(2, p):
        if all(pow(g, (p - 1) // f, p) != 1 for f in fac): return g

class Frob:
    """Z_p x| Z_k, index a*k+b, (a1,b1)(a2,b2) = (a1 + r^b1 a2, b1+b2), r of order k mod p."""
    def __init__(self, p, k):
        assert is_prime(p) and (p - 1) % k == 0
        self.p, self.k = p, k
        g = prim_root(p); r = pow(g, (p - 1) // k, p)
        assert pow(r, k, p) == 1 and r != 1
        self.r = r; self.N = p * k; self.name = f"Frob Z{p} x| Z{k}"
        self.ag = np.arange(self.N, dtype=np.int64) // k
        self.bg = np.arange(self.N, dtype=np.int64) % k
        self.e = 0
        # type: 0 identity, 1 central (none for faithful action), 2 other
        t = np.full(self.N, 2, dtype=np.int8); t[0] = 0; self.type = t
    def lmul(self, s):
        a_s, b_s = divmod(s, self.k)
        rb = pow(self.r, b_s, self.p)
        A = (a_s + rb * self.ag) % self.p
        B = (b_s + self.bg) % self.k
        return A * self.k + B
    def inv(self, s):
        a, b = divmod(s, self.k)
        b2 = (-b) % self.k
        a2 = (-a * pow(self.r, b2, self.p)) % self.p
        return a2 * self.k + b2

class SLn:
    """SL(2,p) x Z_n, index i*n+z with i index of matrix in SL(2,p)."""
    def __init__(self, p, n):
        self.p, self.n = p, n
        mats = []
        for a in range(p):
            for b in range(p):
                for c in range(p):
                    for d in range(p):
                        if (a * d - b * c) % p == 1: mats.append((a, b, c, d))
        self.mats = mats; self.idx = {m: i for i, m in enumerate(mats)}
        self.S = len(mats); self.N = self.S * n; self.name = f"SL(2,{p}) x Z{n}"
        self.ident = self.idx[(1, 0, 0, 1)]; self.mI = self.idx[((p - 1), 0, 0, (p - 1))]
        self.ig = np.arange(self.N, dtype=np.int64) // n
        self.zg = np.arange(self.N, dtype=np.int64) % n
        self.e = self.ident * n
        t = np.full(self.N, 2, dtype=np.int8)
        t[(self.ig == self.ident) | (self.ig == self.mI)] = 1
        t[self.e] = 0; self.type = t
    def _mm(self, x, y):
        p = self.p; a, b, c, d = x; e, f, g, h = y
        return ((a * e + b * g) % p, (a * f + b * h) % p, (c * e + d * g) % p, (c * f + d * h) % p)
    def lmul(self, s):
        i_s, z_s = divmod(s, self.n)
        M = self.mats[i_s]
        tab = np.array([self.idx[self._mm(M, m)] for m in self.mats], dtype=np.int64)
        return tab[self.ig] * self.n + (z_s + self.zg) % self.n
    def inv(self, s):
        i_s, z_s = divmod(s, self.n); a, b, c, d = self.mats[i_s]; p = self.p
        return self.idx[(d, (-b) % p, (-c) % p, a)] * self.n + (-z_s) % self.n

def run(G, Delta, seed, T=10):
    rng = random.Random(seed)
    N = G.N
    S = [G.e]
    while len(S) < Delta:
        s = rng.randrange(N)
        if s != G.e and s not in S: S.append(s)
    LM = [G.lmul(s) for s in S]; LMi = [G.lmul(G.inv(s)) for s in S]
    out = {}
    for side, src in (("A", 0), ("B", 1)):
        dist = np.full(2 * N, -1, dtype=np.int16)
        s0 = src * N + G.e
        dist[s0] = 0
        front = np.array([s0], dtype=np.int64)
        for lvl in range(1, T + 1):
            Af = front[front < N]; Bf = front[front >= N] - N
            cand = [N + LM[j][Af] for j in range(Delta)] + [LMi[j][Bf] for j in range(Delta)]
            new = np.unique(np.concatenate(cand)) if cand else np.array([], dtype=np.int64)
            new = new[dist[new] == -1]
            dist[new] = lvl
            front = new
            if front.size == 0: break
        # per-level A and B counts (same-side ball X_t for t even on the source side)
        same = dist[:N] if side == "A" else dist[N:]
        cnt = {}
        for t in range(0, T + 1, 2):
            cnt[t] = int(np.sum((same >= 0) & (same <= t)))
        unc = (same < 0)
        tyc = {k: int(np.sum(unc & (G.type == v))) for k, v in (("id", 0), ("central", 1), ("other", 2))}
        out[side] = {"ball": cnt, "uncov": tyc}
    return out

def W(Delta, t):
    return 1 + sum(Delta * (Delta - 1) ** (j - 1) for j in range(2, t + 1, 2))

if __name__ == "__main__":
    which = sys.argv[1]; seeds = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    Delta = 4
    fam = {
        "F761x19": lambda: Frob(761, 19),
        "SL23": lambda: SLn(23, 1),
        "SL13x7": lambda: SLn(13, 7),
        "FROB3": lambda: Frob(next(p for p in range(4800, 5000) if is_prime(p) and p % 3 == 1), 3),
        "F907x151": lambda: Frob(907, 151),
    }[which]()
    print(f"{fam.name} N={fam.N} Delta={Delta} seeds={seeds}", flush=True)
    print("model W_t:", {t: W(Delta, t) for t in range(0, 11, 2)}, flush=True)
    res = []
    for sd in range(seeds):
        r = run(fam, Delta, 1000 + sd)
        res.append(r)
        print("seed", sd, "A ball", r["A"]["ball"], "B ball", r["B"]["ball"], flush=True)
        print("   uncov@10 A", r["A"]["uncov"], "B", r["B"]["uncov"], flush=True)
    # averages
    N = fam.N
    avgA = {t: np.mean([r["A"]["ball"][t] for r in res]) for t in range(0, 11, 2)}
    avgB = {t: np.mean([r["B"]["ball"][t] for r in res]) for t in range(0, 11, 2)}
    print("AVG A-ball X_t, model N(1-exp(-W/N)), ratio")
    for t in range(0, 11, 2):
        mdl = N * (1 - math.exp(-W(Delta, t) / N))
        print(f"  t={t:2d} W={W(Delta,t):8d} X_A={avgA[t]:9.1f} X_B={avgB[t]:9.1f} model={mdl:9.1f} A/model={avgA[t]/mdl:.4f} B/model={avgB[t]/mdl:.4f}")
    for side in ("A", "B"):
        for k in ("id", "central", "other"):
            print(side, k, "uncov@10 mean", np.mean([r[side]["uncov"][k] for r in res]))
    print("mu_model at t=10:", N * math.exp(-W(Delta, 10) / N))
