import itertools
import math
import random
import time

import numpy as np

import lib


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
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2.
#
# Vertices: A_{i,g} = i*G + g (i < k), B_{j,h} = (k+j)*G + h.
# Layer l pairs A_i with B_{layers[l][i]} through voltage s: A_{i,g} ~ B_{p,g*s}.
# Every layer is a permutation, so every vertex gets degree d exactly.
#
# Change: the annealing trials now run in a compiled C engine (C_SOURCE). Each
# call anneals one group with random restarts inside a short time slice, so
# far more moves per second are tried than with the Python/numpy loop. The
# Python annealer is kept as a fallback if the C engine cannot be compiled.
# A bandit over base sizes k still chooses where the budget goes.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 32
#define MAXK 8
#define PENALTY 1000LL

static uint64_t rs = 1;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int irand(int n) { return (int)(rnd() % (uint64_t)n); }
static double urand(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_, k_, m_, k2_, G_, N_;
static int rp[64];
static int layers[MAXD][MAXK];
static int S[MAXD][MAXK];
static int *nbr;
static uint32_t *Rc, *Rn, *scrA, *scrB;
static uint32_t FULL;
static unsigned char pc[1 << 16];

/* Group Z_m x| Z_k2, element a*k2+b, (a,b)(c,e) = (a + r^b c, b+e). */
static int gmul(int x, int y) {
    int a = x / k2_, b = x % k2_;
    int c = y / k2_, e = y % k2_;
    int aa = (int)((a + (long long)rp[b] * c) % m_);
    return aa * k2_ + (b + e) % k2_;
}

static int ginv(int x) {
    int a = x / k2_, b = x % k2_;
    int nb = (k2_ - b) % k2_;
    int na = (int)(((long long)rp[nb] * a) % m_);
    na = (m_ - na) % m_;
    return na * k2_ + nb;
}

static void set_layer(int l) {
    int *nb = nbr + (size_t)l * N_;
    for (int i = 0; i < k_; i++) {
        int j = layers[l][i], s = S[l][i];
        int si = ginv(s);
        for (int g = 0; g < G_; g++) {
            nb[i * G_ + g] = (k_ + j) * G_ + gmul(g, s);
            nb[(k_ + j) * G_ + g] = i * G_ + gmul(g, si);
        }
    }
}

static int dupcount(void) {
    int c = 0;
    for (int l = 0; l < d_; l++)
        for (int i = 0; i < k_; i++) {
            int dup = 0;
            for (int l2 = 0; l2 < l && !dup; l2++)
                if (layers[l2][i] == layers[l][i] && S[l2][i] == S[l][i]) dup = 1;
            c += dup;
        }
    return c;
}

/* Reach bitmasks into out; returns cost = unreached pairs + PENALTY * duplicates. */
static long long evaluate(uint32_t *out) {
    int N = N_;
    for (int u = 0; u < N; u++) scrA[u] = 0;
    for (int b = 0; b < 2 * k_; b++) scrA[b * G_] = 1u << b;
    uint32_t *a = scrA, *b2 = scrB;
    for (int t = 0; t < D_; t++) {
        int changed = 0;
        for (int u = 0; u < N; u++) {
            uint32_t r = a[u];
            for (int l = 0; l < d_; l++) r |= a[nbr[(size_t)l * N + u]];
            b2[u] = r;
            changed |= (r != a[u]);
        }
        uint32_t *tmp = a; a = b2; b2 = tmp;
        if (!changed) break;
    }
    long long sum = 0;
    for (int u = 0; u < N; u++) { out[u] = a[u]; sum += pc[a[u] & 0xFFFF]; }
    long long unr = (long long)2 * k_ * N - sum;
    return unr + PENALTY * (long long)dupcount();
}

static void swap_bufs(void) { uint32_t *t = Rc; Rc = Rn; Rn = t; }

static void random_state(void) {
    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < k_; i++) layers[l][i] = i;
        for (int i = k_ - 1; i > 0; i--) {
            int j = irand(i + 1);
            int t = layers[l][i]; layers[l][i] = layers[l][j]; layers[l][j] = t;
        }
        for (int i = 0; i < k_; i++) S[l][i] = irand(G_);
        set_layer(l);
    }
}

static int run_anneal(int iters, int patience, clock_t hard) {
    long long cost = evaluate(Rc);
    double c0 = cost > 1 ? (double)cost : 1.0;
    long long best = cost;
    int last = 0;
    for (int t = 0; t < iters; t++) {
        if (cost == 0) return 1;
        if (t - last > patience) return 0;
        if ((t & 63) == 0 && clock() > hard) return 0;
        double temp = 0.01 * c0 * (1.0 - (double)t / iters);
        if (temp < 0.5) temp = 0.5;

        if (k_ >= 2 && urand() < 0.25) {
            /* Layer-swap move. */
            int l = irand(d_);
            int i1 = irand(k_), i2 = irand(k_ - 1);
            if (i2 >= i1) i2++;
            int tmp = layers[l][i1]; layers[l][i1] = layers[l][i2]; layers[l][i2] = tmp;
            set_layer(l);
            long long c2 = evaluate(Rn);
            if (c2 <= cost || urand() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                swap_bufs();
                if (cost < best) { best = cost; last = t; }
            } else {
                tmp = layers[l][i1]; layers[l][i1] = layers[l][i2]; layers[l][i2] = tmp;
                set_layer(l);
            }
            continue;
        }

        /* Voltage move: defect-targeted with probability 0.4, otherwise uniform. */
        int l = -1, i = -1;
        if (urand() < 0.4) {
            int start = irand(N_);
            for (int q = 0; q < N_; q++) {
                int u = (start + q) % N_;
                if (Rc[u] != FULL) {
                    int block = u / G_;
                    int ll = irand(d_);
                    int ii = -1;
                    if (block < k_) ii = block;
                    else {
                        for (int x = 0; x < k_; x++)
                            if (layers[ll][x] == block - k_) ii = x;
                    }
                    if (ii >= 0) { l = ll; i = ii; }
                    break;
                }
            }
        }
        if (l < 0) { l = irand(d_); i = irand(k_); }

        int old = S[l][i];
        int nw = irand(G_);
        if (nw == old) continue;
        S[l][i] = nw;
        set_layer(l);
        long long c2 = evaluate(Rn);
        if (c2 <= cost || urand() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            swap_bufs();
            if (cost < best) { best = cost; last = t; }
        } else {
            S[l][i] = old;
            set_layer(l);
        }
    }
    return cost == 0;
}

int main(int argc, char **argv) {
    if (argc < 11) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    long long seed = atoll(argv[3]);
    double budget = atof(argv[4]);
    k_ = atoi(argv[5]);
    m_ = atoi(argv[6]);
    k2_ = atoi(argv[7]);
    int r = atoi(argv[8]);
    int iters = atoi(argv[9]);
    int patience = atoi(argv[10]);
    if (d_ < 1 || d_ > MAXD || k_ < 1 || k_ > MAXK || m_ < 2 || k2_ < 1 || k2_ > 63 || D_ < 1) {
        printf("0 0\n");
        return 0;
    }
    G_ = m_ * k2_;
    N_ = 2 * k_ * G_;
    rp[0] = 1 % m_;
    for (int b = 1; b < k2_; b++) rp[b] = (int)(((long long)rp[b - 1] * r) % m_);
    rs = (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    FULL = (1u << (2 * k_)) - 1;
    for (int x = 1; x < (1 << 16); x++) pc[x] = (unsigned char)(pc[x >> 1] + (x & 1));

    nbr = malloc(sizeof(int) * (size_t)d_ * N_);
    Rc = malloc(sizeof(uint32_t) * N_);
    Rn = malloc(sizeof(uint32_t) * N_);
    scrA = malloc(sizeof(uint32_t) * N_);
    scrB = malloc(sizeof(uint32_t) * N_);
    if (!nbr || !Rc || !Rn || !scrA || !scrB) { printf("0 0\n"); return 0; }

    clock_t hard = clock() + (clock_t)(budget * (double)CLOCKS_PER_SEC);
    int found = 0;
    while (!found && clock() < hard) {
        random_state();
        found = run_anneal(iters, patience, hard);
    }
    if (!found) { printf("0 0\n"); return 0; }

    long long M = (long long)k_ * G_ * d_;
    printf("%d %lld\n", N_, M);
    for (int u = 0; u < k_ * G_; u++)
        for (int l = 0; l < d_; l++)
            printf("%d %d\n", u, nbr[(size_t)l * N_ + u]);
    return 0;
}
"""

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)
_SLICE = 2.0  # seconds per C annealing call


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))  # ceil, so the order is at least target
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1  # dihedral-type: (a,b)(c,e) = (a + (-1)^b c, b+e)
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
    """Return (G, Ts, Invs) for Z_m x| Z_k2 (element a*k2+b, (a,b)(c,e) = (a+r^b c, b+e)).

    Ts[s, g] = g*s and Invs[s, h] = the g with g*s = h, built with one numpy broadcast.
    """
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
    """Python fallback: simulated annealing with stagnation restarts. Returns (n, edges) or None."""
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


def _c_search(d, D, k, m, k2, r, seconds, seed):
    """Run the C annealer for one group; returns (n, edges) or None."""
    args = [d, D, seed, f"{seconds:.3f}", k, m, k2, r, 4000, 1200]
    out = lib.run_c(C_SOURCE, args, timeout=seconds + 15.0)
    n, edges = lib.parse_graph_text(out)
    return (n, edges) if n > 0 else None


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

    # Main search with the bandit over base sizes k.
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}
    use_c = True

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
        G = m * k2
        if 2 * k * G <= best_n:
            continue
        trials[k] += 1

        res = None
        if use_c:
            slice_s = min(_SLICE, deadline - time.monotonic())
            if slice_s < 0.2:
                break
            try:
                res = _c_search(d, D, k, m, k2, r, slice_s, rng.randrange(1, 1 << 30))
            except Exception:
                use_c = False  # C engine unavailable: fall back to Python
        if not use_c:
            G2, Ts, Invs = _semidirect_tables(m, k2, r)
            res = _search(d, D, k, G2, Ts, Invs, rng, deadline, 4000, 1200)

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
