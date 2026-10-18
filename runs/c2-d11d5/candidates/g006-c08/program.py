"""Bold variant: a C voltage-lift engine replaces the Python/numpy lift search.

The C side searches bi-Cayley lifts over semidirect products Z_m x| Z_k2 with up to 8 base
blocks per side. It uses simulated annealing over permutations and voltages, with a bandit over
base sizes and an order goal that ratchets upward. Every graph it returns is checked with its own
validator, and the Python side re-checks with lib.is_valid. Exact constructions (projective
planes, Araujo-Pardo-Lopez, W(q)) and K_{d,d} remain as fallbacks.
"""
import itertools
import time

import lib


C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 12288
#define MAXW (MAXN / 64)
#define MAXD 32
#define MAXK 8
#define MAXL 32
#define PEN 1000L
#define ITERS 4000L
#define PATIENCE 900L

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static uint64_t rng_state = 88172645463325252ULL;
static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];
static int queue_buf[MAXN];
static Graph gbest, gtmp;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

/* Number of unordered pairs at distance > D; also sets badv[v]. */
static long bad_pairs(const Graph *g) {
    int n = g->n, W = (n + 63) / 64;
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int i = 0; i < g->deg[v]; i++) {
                const uint64_t *s = cur + (size_t)g->adj[v][i] * W;
                for (int w = 0; w < W; w++) dst[w] |= s[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long total = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *s = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(s[w]);
        badv[v] = n - c;
        total += n - c;
    }
    return total / 2;
}

static int is_valid(const Graph *g) {
    if (g->n <= 0 || g->n > MAXN) return 0;
    for (int v = 0; v < g->n; v++) {
        if (g->deg[v] > d) return 0;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (u < 0 || u >= g->n || u == v || g->side[u] == g->side[v]) return 0;
            for (int j = 0; j < i; j++)
                if (g->adj[v][j] == u) return 0;
        }
    }
    return bad_pairs(g) == 0;
}

static void read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN || m < 0) return;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n ||
            g->deg[u] >= MAXD || g->deg[v] >= MAXD) { g->n = 0; return; }
        add_edge(g, u, v);
    }
    for (int s = 0; s < n; s++) {
        if (g->side[s] != 255) continue;
        int head = 0, tail = 0;
        g->side[s] = 0;
        queue_buf[tail++] = s;
        while (head < tail) {
            int v = queue_buf[head++];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (g->side[u] == 255) { g->side[u] = 1 - g->side[v]; queue_buf[tail++] = u; }
                else if (g->side[u] == g->side[v]) { g->n = 0; return; }
            }
        }
    }
    if (!is_valid(g)) g->n = 0;
}

static void print_graph(const Graph *g) {
    long m = 0;
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++)
            if (u < g->adj[u][i]) m++;
    printf("%d %ld\n", g->n, m);
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++)
            if (u < g->adj[u][i]) printf("%d %d\n", u, g->adj[u][i]);
}

/* ---------- semidirect group Z_m x| Z_k2, element (a,b) coded a*k2+b ---------- */

static int Lk, Lk2, Lm, Lr, Lg, Ncur;
static uint64_t Lfull;
static int Lpow[64];
static int Lnb[MAXL][MAXN];     /* Lnb[l][u]: neighbour of u in layer l */
static int lay[MAXL][MAXK];     /* lay[l][i]: B block joined to A block i in layer l */
static int Sv[MAXL][MAXK];      /* voltage of dart (l, i) */
static uint64_t curR[MAXN], candR[MAXN], scrA[MAXN], scrB[MAXN];
static int cands[MAXN];

static int gmul(int x, int y) {
    int a = x / Lk2, b = x - a * Lk2;
    int c = y / Lk2, e = y - c * Lk2;
    long long t = (long long)Lpow[b] * c + a;
    int aa = (int)(t % Lm);
    int bb = b + e;
    if (bb >= Lk2) bb -= Lk2;
    return aa * Lk2 + bb;
}

static int ginv(int x) {
    int a = x / Lk2, b = x - a * Lk2;
    int nb = (Lk2 - b) % Lk2;
    long long t = (long long)Lpow[nb] * a;
    int aa = (int)((Lm - t % Lm) % Lm);
    return aa * Lk2 + nb;
}

static void set_dart(int l, int i, int p, int s) {
    int G = Lg, k = Lk;
    int si = ginv(s);
    for (int g = 0; g < G; g++) {
        int u = i * G + g;
        Lnb[l][u] = (k + p) * G + gmul(g, s);
        int v = (k + p) * G + g;
        Lnb[l][v] = i * G + gmul(g, si);
    }
}

static void setup_group(int k, int k2, int m, int r) {
    Lk = k; Lk2 = k2; Lm = m; Lr = r;
    Lg = m * k2;
    Ncur = 2 * k * Lg;
    Lfull = (1ULL << (2 * k)) - 1;
    Lpow[0] = 1 % m;
    for (int b = 1; b < k2; b++) Lpow[b] = (int)((long long)Lpow[b - 1] * r % m);
}

static long gcdl(long a, long b) {
    while (b) { long t = a % b; a = b; b = t; }
    return a;
}

static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static const int K2LIST[] = {1, 1, 2, 2, 3, 4, 5, 6, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};

static int sample_group(int k, long target, int *m_o, int *k2_o, int *r_o) {
    int nk = (int)(sizeof(K2LIST) / sizeof(K2LIST[0]));
    for (int tries = 0; tries < 200; tries++) {
        int k2 = K2LIST[rndint(nk)];
        long m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        long G = m * k2;
        if (2L * k * G > MAXN) continue;
        int r = 1;
        if (k2 >= 2 && m >= 3 && rnd01() >= 0.25) {
            int nc = 0;
            for (long c = 2; c < m; c++) {
                if (gcdl(c, m) == 1 && powmod(c, k2, m) == 1 % m) cands[nc++] = (int)c;
            }
            if (nc > 0) r = cands[rndint(nc)];
        }
        *m_o = (int)m;
        *k2_o = k2;
        *r_o = r;
        return 1;
    }
    return 0;
}

static void random_lift(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < Lk; i++) lay[l][i] = i;
        for (int i = Lk - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = lay[l][i];
            lay[l][i] = lay[l][j];
            lay[l][j] = t;
        }
        for (int i = 0; i < Lk; i++) {
            Sv[l][i] = rndint(Lg);
            set_dart(l, i, lay[l][i], Sv[l][i]);
        }
    }
}

/* Count duplicate darts (same A block, B block and voltage in two layers). */
static long dup_count(void) {
    long dup = 0;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < Lk; i++) {
            int p = lay[l][i], s = Sv[l][i];
            int found = 0;
            for (int l2 = 0; l2 < l && !found; l2++)
                if (lay[l2][i] == p && Sv[l2][i] == s) found = 1;
            dup += found;
        }
    return dup;
}

/* Reach bitmasks from block representatives; returns missing (vertex, rep) pairs. */
static long compute_reach(uint64_t *out) {
    int N = Ncur, K2 = 2 * Lk;
    uint64_t *cur = scrA, *nxt = scrB;
    for (int u = 0; u < N; u++) cur[u] = 0;
    for (int b = 0; b < K2; b++) cur[b * Lg] = 1ULL << b;
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int u = 0; u < N; u++) {
            uint64_t x = cur[u];
            for (int l = 0; l < d; l++) x |= cur[Lnb[l][u]];
            nxt[u] = x;
            changed |= (x != cur[u]);
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
        if (!changed) break;
    }
    memcpy(out, cur, sizeof(uint64_t) * (size_t)N);
    long cost = 0;
    for (int u = 0; u < N; u++) cost += K2 - __builtin_popcountll(cur[u]);
    return cost;
}

static long eval_full(uint64_t *out) {
    return compute_reach(out) + PEN * dup_count();
}

static int sa_run(long iters, long patience) {
    int N = Ncur;
    long cost = eval_full(curR);
    long c0 = cost > 1 ? cost : 1;
    long best = cost, last = 0;
    uint64_t *cand = candR;
    for (long t = 0; t < iters; t++) {
        if (cost == 0) break;
        if ((t & 31) == 0 && now() > t_end) break;
        if (t - last > patience) break;
        double temp = 0.01 * (double)c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;
        double x = rnd01();

        if (Lk >= 2 && x < 0.25) {
            int l = rndint(d);
            int i1 = rndint(Lk), i2 = rndint(Lk - 1);
            if (i2 >= i1) i2++;
            int t1 = lay[l][i1];
            lay[l][i1] = lay[l][i2];
            lay[l][i2] = t1;
            set_dart(l, i1, lay[l][i1], Sv[l][i1]);
            set_dart(l, i2, lay[l][i2], Sv[l][i2]);
            long c2 = eval_full(cand);
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                memcpy(curR, cand, sizeof(uint64_t) * (size_t)N);
                if (cost < best) { best = cost; last = t; }
            } else {
                t1 = lay[l][i1];
                lay[l][i1] = lay[l][i2];
                lay[l][i2] = t1;
                set_dart(l, i1, lay[l][i1], Sv[l][i1]);
                set_dart(l, i2, lay[l][i2], Sv[l][i2]);
            }
            continue;
        }

        int l = -1, i = -1, targeted = 0;
        if (rnd01() < 0.4) {
            for (int tries = 0; tries < 30 && !targeted; tries++) {
                int u = rndint(N);
                if (curR[u] == Lfull) continue;
                int b = u / Lg;
                if (b < Lk) {
                    i = b;
                    l = rndint(d);
                    targeted = 1;
                } else {
                    int p = b - Lk;
                    l = rndint(d);
                    for (int ii = 0; ii < Lk; ii++)
                        if (lay[l][ii] == p) { i = ii; break; }
                    if (i >= 0) targeted = 1;
                }
            }
        }
        if (!targeted) {
            l = rndint(d);
            i = rndint(Lk);
        }
        int old = Sv[l][i];
        int nw = rndint(Lg);
        if (nw == old) continue;
        Sv[l][i] = nw;
        set_dart(l, i, lay[l][i], nw);
        long c2 = eval_full(cand);
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            memcpy(curR, cand, sizeof(uint64_t) * (size_t)N);
            if (cost < best) { best = cost; last = t; }
        } else {
            Sv[l][i] = old;
            set_dart(l, i, lay[l][i], old);
        }
    }
    return cost == 0;
}

static int build_graph(Graph *g) {
    int A = Lk * Lg, N = 2 * A;
    if (N > MAXN) return 0;
    g->n = N;
    for (int v = 0; v < N; v++) {
        g->deg[v] = 0;
        g->side[v] = (unsigned char)(v < A ? 0 : 1);
    }
    for (int u = 0; u < A; u++)
        for (int l = 0; l < d; l++) {
            int v = Lnb[l][u];
            if (g->deg[u] >= MAXD || g->deg[v] >= MAXD) return 0;
            add_edge(g, u, v);
        }
    return 1;
}

static int pick_k(const int *trials, const int *wins) {
    if (rnd01() < 0.2) return 1 + rndint(MAXK);
    int best = 1;
    double bs = -1.0;
    for (int k = 1; k <= MAXK; k++) {
        double s = (wins[k] + 1.0) / (trials[k] + 2.0) + 0.02 * rnd01();
        if (s > bs) { bs = s; best = k; }
    }
    return best;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    double budget = limit * 0.9 - 0.5;
    if (budget < 0.2) budget = 0.2;
    t_end = t0 + budget;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 2 || d > MAXD) { printf("0 0\n"); return 0; }
    gbest.n = 0;
    read_start(&gbest);

    double goal_d = gbest.n > 0 ? gbest.n * 1.02 + 1.0 : 2.0 * d;
    if (goal_d < 4.0) goal_d = 4.0;
    int trials[MAXK + 1], wins[MAXK + 1];
    for (int k = 0; k <= MAXK; k++) { trials[k] = 0; wins[k] = 0; }

    while (now() < t_end) {
        int k = pick_k(trials, wins);
        long target = (long)(goal_d / (2.0 * k)) + (long)rndint(3);
        if (target < 2) target = 2;
        int m, k2, r;
        if (!sample_group(k, target, &m, &k2, &r)) {
            goal_d *= 0.99;
            continue;
        }
        setup_group(k, k2, m, r);
        if (Ncur <= gbest.n) {
            if (goal_d < gbest.n * 1.02) goal_d = gbest.n * 1.02;
            continue;
        }
        trials[k]++;
        random_lift();
        int ok = sa_run(ITERS, PATIENCE);
        if (ok && build_graph(&gtmp) && is_valid(&gtmp) && gtmp.n > gbest.n) {
            gbest = gtmp;
            wins[k]++;
            goal_d = gtmp.n * 1.04;
        } else {
            double floor_d = gbest.n * 1.02;
            double nd = goal_d * 0.995;
            goal_d = nd > floor_d ? nd : floor_d;
        }
        if (goal_d > MAXN - 64) goal_d = MAXN - 64;
    }

    if (gbest.n > 0) print_graph(&gbest);
    else printf("0 0\n");
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Exact constructions.
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


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        try:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
                if D == 3 and lib.is_prime_power(d - 1):
                    return best
        except Exception:
            pass
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass
    if D == 4:
        try:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    consider(*_gq_w(q))
                    break
        except Exception:
            pass

    # Main search: the C engine runs voltage-lift search over semidirect groups,
    # starting from the best exact graph found so far.
    remaining = 0.85 * time_limit - 3.0 - (time.monotonic() - t0)
    if remaining > 2.0 and d <= 32:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2)],
                             stdin_graph=best, timeout=remaining + 3.0)
            out = lib.parse_graph_text(text)
            consider(out[0], out[1])
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
