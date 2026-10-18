import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# C engine: random bi-regular bipartite graphs, grown from small size.
#
# The graph is d layers of permutations sigma_l between side A (0..H-1) and
# side B (H..2H-1). Every vertex has degree d (multi-edges are penalised, and
# only duplicate-free states are ever reported). Local search swaps two targets
# of one permutation, minimising unordered pairs at distance > D plus duplicate
# edges. The size grows by adjacent extensions (warm start) with an adaptive
# step; the last valid state is printed.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define DMAX 64
#define HMAX 6000
#define S (HMAX + 2)
#define NMAX (2 * HMAX + 2)
#define WMAX ((NMAX + 63) / 64)

static int d_, D_, H;
static int sig[DMAX * S];
static int isig[DMAX * S];
static int bsig[DMAX * HMAX];
static int bH;
static u64 *RA, *RB;
static int *POP, *POPN;
static u64 *mark;
static u64 stamp = 0;
static u64 rs = 1;
static double DEADLINE;

static u64 next_rand(void) {
    u64 z = (rs += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

static int rnd_int(int n) { return (int)(next_rand() % (u64)n); }

static double rnd_dbl(void) {
    return (double)(next_rand() >> 11) * (1.0 / 9007199254740992.0);
}

static double now_s(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static void init_random(void) {
    for (int l = 0; l < d_; l++) {
        int *s = sig + l * S, *is = isig + l * S;
        for (int a = 0; a < H; a++) s[a] = a;
        for (int a = H - 1; a > 0; a--) {
            int j = rnd_int(a + 1);
            int t = s[a]; s[a] = s[j]; s[j] = t;
        }
        for (int a = 0; a < H; a++) is[s[a]] = a;
    }
}

static void do_swap(int l, int a1, int a2) {
    int *s = sig + l * S, *is = isig + l * S;
    int b1 = s[a1], b2 = s[a2];
    s[a1] = b2; s[a2] = b1;
    is[b1] = a2; is[b2] = a1;
}

/* Extend H -> H+1 keeping every layer a permutation. */
static void extend_one(void) {
    for (int l = 0; l < d_; l++) {
        int *s = sig + l * S, *is = isig + l * S;
        int j = rnd_int(H);
        int bold = s[j];
        s[H] = bold; is[bold] = H;
        s[j] = H;    is[H] = j;
    }
    H++;
}

/* Returns unordered unreached pairs + duplicate edges; fills pop[v] = |ball_D(v)|. */
static long eval_state(int *pop) {
    int n = 2 * H;
    int W = (n + 63) >> 6;
    u64 *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(u64) * (size_t)n * (size_t)W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + (v >> 6)] = 1ULL << (v & 63);
    for (int r = 0; r < D_; r++) {
        for (int v = 0; v < n; v++) {
            u64 *dst = nxt + (size_t)v * W;
            const u64 *src = cur + (size_t)v * W;
            memcpy(dst, src, sizeof(u64) * (size_t)W);
            for (int l = 0; l < d_; l++) {
                int u = (v < H) ? H + sig[l * S + v] : isig[l * S + (v - H)];
                const u64 *s2 = cur + (size_t)u * W;
                for (int w = 0; w < W; w++) dst[w] |= s2[w];
            }
        }
        u64 *t = cur; cur = nxt; nxt = t;
    }
    long unreached = 0;
    for (int v = 0; v < n; v++) {
        const u64 *row = cur + (size_t)v * W;
        int c = 0;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(row[w]);
        pop[v] = c;
        unreached += n - c;
    }
    long dup = 0;
    for (int a = 0; a < H; a++) {
        stamp++;
        for (int l = 0; l < d_; l++) {
            int x = sig[l * S + a];
            if (mark[x] == stamp) dup++;
            else mark[x] = stamp;
        }
    }
    return unreached / 2 + dup;
}

/* Simulated annealing at the current H. Returns 1 if a valid state was reached. */
static int anneal(long maxmoves) {
    int n = 2 * H;
    long cost = eval_state(POP);
    for (long mv = 0; mv < maxmoves && cost > 0; mv++) {
        if ((mv & 7) == 0 && now_s() > DEADLINE) break;
        int l = rnd_int(d_);
        int a1 = -1;
        if (rnd_dbl() < 0.5) {
            int u = -1;
            for (int t = 0; t < 40; t++) {
                int c = rnd_int(n);
                if (POP[c] < n) { u = c; break; }
            }
            if (u >= 0) a1 = (u < H) ? u : isig[l * S + (u - H)];
        }
        if (a1 < 0) a1 = rnd_int(H);
        int a2 = rnd_int(H);
        if (a2 == a1) continue;
        do_swap(l, a1, a2);
        long nc = eval_state(POPN);
        long delta = nc - cost;
        double temp = 0.7 * (1.0 - (double)mv / (double)maxmoves) + 0.05;
        if (delta <= 0 || rnd_dbl() < exp(-(double)delta / temp)) {
            cost = nc;
            int *t = POP; POP = POPN; POPN = t;
        } else {
            do_swap(l, a1, a2);
        }
    }
    return cost == 0;
}

static void save_backup(void) {
    bH = H;
    for (int l = 0; l < d_; l++)
        for (int a = 0; a < H; a++)
            bsig[l * HMAX + a] = sig[l * S + a];
}

static void restore_backup(void) {
    H = bH;
    for (int l = 0; l < d_; l++) {
        for (int a = 0; a < H; a++) {
            int b = bsig[l * HMAX + a];
            sig[l * S + a] = b;
            isig[l * S + b] = a;
        }
    }
}

static void print_backup(void) {
    int n = 2 * bH;
    long m = (long)bH * d_;
    printf("%d %ld\n", n, m);
    for (int a = 0; a < bH; a++)
        for (int l = 0; l < d_; l++)
            printf("%d %d\n", a, bH + bsig[l * HMAX + a]);
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    u64 seed = (u64)strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    if (d_ < 2 || d_ > DMAX || D_ < 2) { printf("0 0\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    DEADLINE = now_s() + tl;

    RA = malloc(sizeof(u64) * (size_t)NMAX * WMAX);
    RB = malloc(sizeof(u64) * (size_t)NMAX * WMAX);
    POP = malloc(sizeof(int) * NMAX);
    POPN = malloc(sizeof(int) * NMAX);
    mark = calloc(S, sizeof(u64));
    if (!RA || !RB || !POP || !POPN || !mark) { printf("0 0\n"); return 0; }

    H = d_;
    init_random();
    int ok = 0;
    while (!ok && now_s() < DEADLINE) ok = anneal(400 + H / 2);
    if (!ok) { printf("0 0\n"); return 0; }
    save_backup();

    int s = 4;
    while (now_s() < DEADLINE && H + s < HMAX) {
        for (int k = 0; k < s; k++) extend_one();
        ok = anneal(400 + H / 2);
        if (ok) {
            save_backup();
            if (s < 64) s *= 2;
        } else {
            restore_backup();
            s /= 2;
            if (s < 1) s = 1;
        }
    }
    print_backup();
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Safe baseline families.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Slack extension: add new vertices using spare degree, accepting only
# graphs that pass lib.is_valid.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """Return the 2-colouring of the graph, or None if it is not bipartite."""
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
    """Greedily add new vertices using spare degree; returns (n, edges), always valid."""
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
                w = n
                cand = edges + [(v, w) for v in pick]
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
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2 (older search).
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4, 5, 6)


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
                r = None
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
    """Return (G, Ts, Invs) for Z_m x| Z_k2 (element a*k2+b, (a,b)(c,e) = (a+r^b c, b+e))."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    """Write layer l's neighbours for base vertex i (A side) and base vertex j (B side) with voltage s."""
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach(k, G, D, nbr, d):
    """Bitmask per vertex: bit b is set when representative block b is within distance D."""
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
    """Number of unreached (representative, vertex) pairs."""
    return 2 * k * N - int(_POP[reach].sum())


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters, patience):
    """Simulated annealing with stagnation restarts. Returns (n, edges) or None."""
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


# ----------------------------------------------------------------------------
# New construction driver: C growth of random bi-regular bipartite graphs.
# ----------------------------------------------------------------------------

def _grow_c(d, D, seed, seconds):
    """Run the C growth engine for about `seconds`; return (n, edges) or None."""
    if seconds < 2.0:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, D, int(seed) % (2 ** 31), f"{seconds:.2f}"],
                        stdin_graph=None, timeout=seconds + 10.0)
        n, e = lib.parse_graph_text(out)
        if n < 2 or not e:
            return None
        return n, e
    except Exception:
        return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    final_deadline = start + max(1.0, time_limit - 3.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions: return immediately (calibration-style cases).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # New, different construction for the weak large-D cases: C search over
    # random bi-regular bipartite graphs grown from small size.
    if D >= 5 and d >= 3:
        left = deadline - time.monotonic()
        if left > 8.0:
            res = _grow_c(d, D, seed, 0.6 * left)
            if res is not None:
                consider(res[0], res[1])

    # Older bi-Cayley search with the bandit over base sizes k.
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < deadline:
        k = pick_k()
        base = best_n // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * k * G <= best_n:
            continue
        trials[k] += 1
        res = _search(d, D, k, G, Ts, Invs, rng, deadline, 4000, 1200)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    # Use any spare degree in the best graph to add vertices.
    if time.monotonic() < final_deadline:
        n2, e2 = _slack_extend(best[0], best[1], d, D, rng, final_deadline)
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
