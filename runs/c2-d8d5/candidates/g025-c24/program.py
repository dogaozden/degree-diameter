import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# C engine: voltage-lift annealer over semidirect products Z_m x| Z_k2.
#
# A candidate is a lift of a base bipartite graph with k vertices per side.
# Layer l is a perfect matching sigma_l between the A-side and B-side base
# vertices, with a group voltage g_{l,i} on each A-side base vertex i. The lift
# has vertices (side, i, x), x in G, and edges (A,i,x) -- (B,sigma_l(i), x*g).
# Every vertex has degree d. Left translation by G is an automorphism, so the
# distance condition only needs BFS from the 2k base identities.
#
# Cost = (unreached pairs from those sources) + 10000 * (duplicate darts).
# Simulated annealing moves voltages and swaps targets inside one layer.
# The candidates are given in argv in increasing order of order; the first
# valid lift found for each candidate is kept, and the largest valid one wins.
# ----------------------------------------------------------------------------

C_LIFT = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXL 64
#define MAXK 16
#define MAXK2 64

typedef uint64_t u64;
static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (u64)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_, k_, G_, M_, K2_, NV_;
static int pw_[MAXK2];
static int sig_[MAXL][MAXK], isig_[MAXL][MAXK];
static int volt_[MAXL][MAXK], vinv_[MAXL][MAXK];
static int *dist_ = NULL, *queue_ = NULL;

static int gmul(int x, int y) {
    int a = x / K2_, b = x % K2_;
    int c = y / K2_, e = y % K2_;
    int a2 = (int)(((long long)a + (long long)pw_[b] * c) % M_);
    int b2 = (b + e) % K2_;
    return a2 * K2_ + b2;
}

static int ginv(int x) {
    int a = x / K2_, b = x % K2_;
    int nb = (K2_ - b) % K2_;
    int t = (int)(((long long)pw_[nb] * a) % M_);
    int ai = (M_ - t) % M_;
    return ai * K2_ + nb;
}

static void set_volt(int l, int i, int g) {
    volt_[l][i] = g;
    vinv_[l][i] = ginv(g);
}

static void sync_isig(int l) {
    for (int i = 0; i < k_; i++) isig_[l][sig_[l][i]] = i;
}

static int dupcount(void) {
    int dup = 0;
    for (int i = 0; i < k_; i++)
        for (int l1 = 0; l1 < d_; l1++)
            for (int l2 = l1 + 1; l2 < d_; l2++)
                if (sig_[l1][i] == sig_[l2][i] && volt_[l1][i] == volt_[l2][i]) dup++;
    return dup;
}

/* Number of lift vertices at distance > D_ from the identity of base vertex (s0, i0). */
static int bfs_unreached(int s0, int i0) {
    int NV = NV_;
    int src = (s0 * k_ + i0) * G_;
    for (int v = 0; v < NV; v++) dist_[v] = -1;
    int h = 0, t = 0, reached = 1;
    dist_[src] = 0;
    queue_[t++] = src;
    while (h < t) {
        int v = queue_[h++];
        int dv = dist_[v];
        if (dv >= D_) continue;
        int base = v / G_;
        int x = v - base * G_;
        int s = base / k_;
        int i = base - s * k_;
        for (int l = 0; l < d_; l++) {
            int u;
            if (s == 0) {
                int j = sig_[l][i];
                u = (k_ + j) * G_ + gmul(x, volt_[l][i]);
            } else {
                int i2 = isig_[l][i];
                u = i2 * G_ + gmul(x, vinv_[l][i2]);
            }
            if (dist_[u] < 0) {
                dist_[u] = dv + 1;
                queue_[t++] = u;
                reached++;
            }
        }
    }
    return NV - reached;
}

static long long evalcost(void) {
    long long c = 0;
    for (int s = 0; s < 2; s++)
        for (int i = 0; i < k_; i++) c += bfs_unreached(s, i);
    c += 10000LL * (long long)dupcount();
    return c;
}

/* Anneal one candidate for `budget` CPU seconds. Returns 1 if a valid lift is in the state. */
static int search_one(int M, int K2, int R, int k, int d, double budget) {
    M_ = M; K2_ = K2; k_ = k; d_ = d;
    G_ = M * K2;
    NV_ = 2 * k * G_;
    pw_[0] = 1 % M_;
    for (int t = 1; t < K2_; t++) pw_[t] = (int)(((long long)pw_[t - 1] * (R % M_)) % M_);

    free(dist_);
    free(queue_);
    dist_ = malloc(sizeof(int) * (size_t)NV_);
    queue_ = malloc(sizeof(int) * (size_t)NV_);
    if (!dist_ || !queue_) return 0;

    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < k_; i++) sig_[l][i] = i;
        for (int i = k_ - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = sig_[l][i]; sig_[l][i] = sig_[l][j]; sig_[l][j] = t;
        }
        for (int i = 0; i < k_; i++) set_volt(l, i, rint_(G_));
        sync_isig(l);
    }

    long long cost = evalcost();
    double T0 = 2.0 + 0.02 * (double)cost;
    const double T1 = 0.3;
    clock_t s0 = clock();
    while (1) {
        double el = (double)(clock() - s0) / CLOCKS_PER_SEC;
        if (el >= budget) break;
        if (cost == 0) return 1;
        double T = T0 * pow(T1 / T0, el / budget);

        if (k_ >= 2 && rdbl() < 0.3) {
            int l = rint_(d_);
            int i1 = rint_(k_);
            int i2 = rint_(k_ - 1);
            if (i2 >= i1) i2++;
            int t = sig_[l][i1]; sig_[l][i1] = sig_[l][i2]; sig_[l][i2] = t;
            sync_isig(l);
            long long nc = evalcost();
            long long delta = nc - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cost = nc;
            } else {
                t = sig_[l][i1]; sig_[l][i1] = sig_[l][i2]; sig_[l][i2] = t;
                sync_isig(l);
            }
        } else {
            int l = rint_(d_);
            int i = rint_(k_);
            int old = volt_[l][i];
            int nv = rint_(G_);
            if (nv == old) continue;
            set_volt(l, i, nv);
            long long nc = evalcost();
            long long delta = nc - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cost = nc;
            } else {
                set_volt(l, i, old);
            }
        }
    }
    return cost == 0;
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    int ncand = atoi(argv[5]);
    if (d < 1 || d > MAXL || D < 1 || ncand < 0 || argc < 6 + 4 * ncand) {
        printf("0 0\n");
        return 0;
    }
    d_ = d;
    D_ = D;

    int bestN = 0, bestM = 0;
    int *bEu = NULL, *bEv = NULL;
    clock_t c0 = clock();

    for (int c = 0; c < ncand; c++) {
        int M = atoi(argv[6 + 4 * c]);
        int K2 = atoi(argv[7 + 4 * c]);
        int R = atoi(argv[8 + 4 * c]);
        int k = atoi(argv[9 + 4 * c]);
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        double left = limit - el;
        if (left <= 0.05) break;
        double budget = left / (double)(ncand - c);
        if (M < 1 || K2 < 1 || K2 > MAXK2 || k < 1 || k > MAXK || M * K2 < 2) continue;
        if (R < 1) R = 1;

        if (!search_one(M, K2, R, k, d, budget)) continue;
        int NV = 2 * k * G_;
        if (NV <= bestN) continue;

        int cnt = 0;
        int cap = k * G_ * d_;
        int *nu = malloc(sizeof(int) * (size_t)cap);
        int *nw = malloc(sizeof(int) * (size_t)cap);
        if (!nu || !nw) { free(nu); free(nw); continue; }
        for (int i = 0; i < k; i++)
            for (int x = 0; x < G_; x++)
                for (int l = 0; l < d_; l++) {
                    int u = i * G_ + x;
                    int j = sig_[l][i];
                    int v = (k + j) * G_ + gmul(x, volt_[l][i]);
                    nu[cnt] = u;
                    nw[cnt] = v;
                    cnt++;
                }
        free(bEu);
        free(bEv);
        bEu = nu;
        bEv = nw;
        bestN = NV;
        bestM = cnt;
    }

    if (bestN == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", bestN, bestM);
    for (int i = 0; i < bestM; i++) printf("%d %d\n", bEu[i], bEv[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _bipartition(n, adj):
    """2-colouring of the graph, or None if it is not bipartite."""
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
                elif color[v] == color[u]:
                    return None
    return color


def _slack_extend(n, edges, d, D, rng, deadline):
    """Greedily add vertices using spare degree; returns a valid (n, edges)."""
    edges = [tuple(e) for e in edges]
    adj = lib.adjacency(n, edges)
    color = _bipartition(n, adj)
    if color is None:
        return n, edges
    deg = [len(a) for a in adj]
    grew = True
    while grew and time.monotonic() < deadline:
        grew = False
        for side in (0, 1):
            spare = [v for v in range(n) if color[v] == side and deg[v] < d]
            if len(spare) < d:
                continue
            for _ in range(30):
                if time.monotonic() > deadline or len(spare) < d:
                    break
                pick = rng.sample(spare, d)
                cand = edges + [(v, n) for v in pick]
                if lib.is_valid(n + 1, cand, d, D):
                    edges = cand
                    n += 1
                    color.append(1 - side)
                    deg.append(d)
                    for v in pick:
                        deg[v] += 1
                    spare = [v for v in spare if deg[v] < d]
                    grew = True
                    break
    return n, edges


# ----------------------------------------------------------------------------
# Lift candidates for the C voltage annealer.
# ----------------------------------------------------------------------------

def _semidirect_option(G, rng):
    """Return (m, k2, r) with m * k2 = G and a random valid r, or None."""
    opts = []
    for k2 in range(2, min(G, 16) + 1):
        if G % k2:
            continue
        m = G // k2
        if m < 3:
            continue
        for _ in range(40):
            r = rng.randrange(2, m)
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                opts.append((m, k2, r))
                break
    return rng.choice(opts) if opts else None


def _lift_candidates(best_n, rng, cap=20):
    """Candidates (N, k, M, K2, R) with N = 2*k*G > best_n, in increasing N."""
    lo = best_n + 2
    cands = []
    for k in (1, 2, 3, 4, 5, 6, 8):
        glo = max(2, -(-lo // (2 * k)))
        for G in range(glo, glo + 3):
            cands.append((2 * k * G, k, G, 1, 1))
            sd = _semidirect_option(G, rng)
            if sd is not None:
                cands.append((2 * k * G, k, sd[0], sd[1], sd[2]))
    cands.sort()
    return cands[:cap]


def _grow_lift(d, D, seed, seconds, cands):
    """Run the C voltage-lift annealer over the candidates; returns parsed (n, edges)."""
    args = [d, D, seed, f"{seconds:.2f}", len(cands)]
    for _, k, M, K2, R in cands:
        args += [M, K2, R, k]
    out = lib.run_c(C_LIFT, args, stdin_graph=None, timeout=seconds + 20.0)
    return lib.parse_graph_text(out)


# ----------------------------------------------------------------------------
# Python bi-Cayley annealer over semidirect products (fallback phase).
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1
            if math.gcd(r, m) != 1 or pow(r, 2, m) != 1 % m:
                continue
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        return m, k2, r
    return None


def _semidirect_tables(m, k2, r):
    """Return (G, Ts, Invs) for Z_m x| Z_k2 with element a*k2+b."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)  # Ts[s, g] = g*s
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach(k, G, D, nbr, d):
    N = nbr.shape[1]
    reach = np.zeros(N, dtype=np.int64)
    for b in range(2 * k):
        reach[b * G] = 1 << b
    for _ in range(D):
        new = reach.copy()
        for l in range(d):
            new |= reach[nbr[l]]
        if np.array_equal(new, reach):
            break
        reach = new
    return reach


def _unreached(k, N, reach):
    return 2 * k * N - int(_POP[reach].sum())


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters, patience):
    """Simulated annealing over voltages and layer permutations. Returns (n, edges) or None."""
    N = 2 * k * G
    full = (1 << (2 * k)) - 1
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    def dupcount():
        keys = [(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)]
        return len(keys) - len(set(keys))

    reach = _reach(k, G, D, nbr, d)
    cost = _unreached(k, N, reach) + _PENALTY * dupcount()
    c0 = float(max(cost, 1))
    best_cost = cost
    last_improve = 0

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        if t - last_improve > patience:
            break
        temp = max(0.5, 0.01 * c0 * (1.0 - t / iters))
        x = rng.random()

        if k >= 2 and x < 0.25:
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
            _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            r2 = _reach(k, G, D, nbr, d)
            c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost, reach = c2, r2
                if cost < best_cost:
                    best_cost, last_improve = cost, t
            else:
                layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
                _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
                _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            continue

        bad = np.flatnonzero(reach != full) if rng.random() < 0.4 else None
        if bad is not None and bad.size:
            u = int(bad[rng.randrange(bad.size)])
            block = u // G
            l = rng.randrange(d)
            if block < k:
                i = block
            else:
                i = layers[l].index(block - k)
        else:
            l = rng.randrange(d)
            i = rng.randrange(k)

        old = S[l][i]
        new = rng.randrange(G)
        if new == old:
            continue
        S[l][i] = new
        _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], new)
        r2 = _reach(k, G, D, nbr, d)
        c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost, reach = c2, r2
            if cost < best_cost:
                best_cost, last_improve = cost, t
        else:
            S[l][i] = old
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], old)

    if cost != 0:
        return None
    edges = set()
    for u in range(k * G):
        for v in nbr[:, u]:
            edges.add((u, int(v)))
    return N, sorted(edges)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}, valid for D >= 2

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact construction for D = 3 (calibration case): return immediately.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Phase 1 (fallback): Python bi-Cayley annealing with a bandit over base sizes k.
    py_end = t0 + max(1.0, min(0.25 * time_limit, time_limit - 25.0))
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < py_end:
        k = pick_k()
        base = best[0] // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * k * G <= best[0]:
            continue
        trials[k] += 1
        res = _search(d, D, k, G, Ts, Invs, rng, py_end, 4000, 1200)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    # Phase 2 (main): C voltage-lift search for orders above the current best.
    remaining = time_limit - (time.monotonic() - t0) - 8.0
    if remaining >= 3.0:
        cands = _lift_candidates(best[0], rng)
        if cands:
            try:
                n2, e2 = _grow_lift(d, D, rng.randrange(1, 1 << 30), remaining * 0.8, cands)
                consider(n2, e2)
            except Exception:
                pass  # keep the valid fallback

    # Phase 3: use spare degree of the best graph.
    slack_end = t0 + time_limit - 4.0
    if time.monotonic() < slack_end - 2.0:
        n3, e3 = _slack_extend(best[0], best[1], d, D, rng, slack_end)
        consider(n3, e3)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
