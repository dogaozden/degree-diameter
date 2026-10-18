"""Combined program: a C bi-Cayley voltage-lift annealer over semidirect products, then a C
grow-by-two phase that inserts vertices into the best graph found.

The lift search now runs entirely in C. Each candidate is an (m x| k2) group with k blocks per
side and d random permutation layers with voltages. Validity is checked with bitmask distance
propagation. Every returned graph is checked with lib.is_valid, and K_{d,d} (or an exact
construction for D = 3 or 4) is the fallback.
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

#define MAXN 8192
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXK 32

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

static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

static int has_edge(const Graph *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == v) return 1;
    return 0;
}

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

static void del_half(Graph *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == v) {
            g->adj[u][i] = g->adj[u][--g->deg[u]];
            return;
        }
}

static void del_edge(Graph *g, int u, int v) {
    del_half(g, u, v);
    del_half(g, v, u);
}

static void copy_graph(Graph *dst, const Graph *src) {
    dst->n = src->n;
    for (int v = 0; v < src->n; v++) {
        dst->deg[v] = src->deg[v];
        dst->side[v] = src->side[v];
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * src->deg[v]);
    }
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
    static int queue[MAXN];
    for (int s = 0; s < n; s++) {
        if (g->side[s] != 255) continue;
        int head = 0, tail = 0;
        g->side[s] = 0;
        queue[tail++] = s;
        while (head < tail) {
            int v = queue[head++];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (g->side[u] == 255) { g->side[u] = 1 - g->side[v]; queue[tail++] = u; }
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

/* ---------------- grow-by-two phase ---------------- */

static double t_end;
static Graph gbest, gwork;
static int used[MAXN];
static int stamp = 0;

/* One grow-by-two attempt starting from best; on success work holds n+2 valid vertices. */
static int grow_once(const Graph *best, Graph *work, double until) {
    int n = best->n;
    if (n + 2 > moore_bound() || n + 2 > MAXN) return 0;
    copy_graph(work, best);
    int x = n, y = n + 1;
    work->n = n + 2;
    work->deg[x] = work->deg[y] = 0;
    work->side[x] = 0;
    work->side[y] = 1;
    add_edge(work, x, y);
    stamp++;
    used[x] = used[y] = stamp;
    for (int k = 0, tries = 0; k < d - 1 && tries < 100000; tries++) {
        int a = rndint(n);
        if (work->side[a] != 0 || used[a] == stamp || work->deg[a] == 0) continue;
        int b = work->adj[a][rndint(work->deg[a])];
        if (used[b] == stamp || b >= n) continue;
        del_edge(work, a, b);
        add_edge(work, x, b);
        add_edge(work, y, a);
        used[a] = used[b] = stamp;
        k++;
    }
    long bad = bad_pairs(work);
    double T = 1.0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        int v = rndint(work->n);
        for (int tries = 0; tries < 30 && badv[v] == 0; tries++) v = rndint(work->n);
        if (work->deg[v] == 0) continue;
        int u = work->adj[v][rndint(work->deg[v])];
        int s = rndint(work->n);
        if (work->side[s] != work->side[v] || s == v || work->deg[s] == 0) continue;
        int t = work->adj[s][rndint(work->deg[s])];
        if (t == u || has_edge(work, v, t) || has_edge(work, s, u)) continue;
        del_edge(work, v, u);
        del_edge(work, s, t);
        add_edge(work, v, t);
        add_edge(work, s, u);
        long nb = bad_pairs(work);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
        } else {
            del_edge(work, v, t);
            del_edge(work, s, u);
            add_edge(work, v, u);
            add_edge(work, s, t);
        }
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    return is_valid(work);
}

static void grow_search(double until) {
    while (now() < until && gbest.n + 2 <= moore_bound()) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(&gbest, &gwork, now() + slice)) copy_graph(&gbest, &gwork);
    }
}

/* ---------------- bi-Cayley lift search (new in this version) ----------------
 * Group Z_GM x| Z_GK with r = GR (r^GK = 1 mod GM). Element x = a*GK + b; identity is 0.
 * Blocks: A_i (i < K) = i*G + g, B_p = (K+p)*G + h.
 * Layer l pairs A_i with B_{perm[l][i]} via voltage vol[l][i]: A_{i,g} ~ B_{p, g*s}.
 * Left multiplication is an automorphism, so validity reduces to reps: the lift is
 * valid iff every vertex is within distance D of every block representative (index b*G).
 */

static int K, G, NN;
static int GM, GK, GR;
static long rpow[64];
static int perm[MAXD][MAXK];
static int vol[MAXD][MAXK];
static int nbuf[MAXD * MAXN];
static uint64_t rbuf1[MAXN], rbuf2[MAXN];
static uint64_t *reach_res = NULL;
static double lift_deadline;
static Graph cand;
static long trials_[MAXK + 1], wins_[MAXK + 1];

static long gcd_l(long a, long b) {
    while (b) { long t = a % b; a = b; b = t; }
    return a;
}

static long powmod_l(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    long aa = ((long)a + rpow[b] * (long)c) % GM;
    return (int)aa * GK + (b + e) % GK;
}

static int choose_group(int target) {
    static const int ks[] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};
    for (int tries = 0; tries < 200; tries++) {
        int k2 = ks[rndint(20)];
        int m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        int r = 1;
        if (k2 > 1) {
            int found = 0;
            for (int t2 = 0; t2 < 80 && !found; t2++) {
                long c = (t2 == 0) ? 1 : 1 + rndint(m - 1);
                if (gcd_l(c, m) == 1 && powmod_l(c, k2, m) == 1 % m) {
                    r = (int)c;
                    found = 1;
                }
            }
            if (!found) continue;
        }
        GM = m;
        GK = k2;
        GR = r;
        G = GM * GK;
        rpow[0] = 1 % GM;
        for (int b = 1; b < GK; b++) rpow[b] = rpow[b - 1] * GR % GM;
        return 1;
    }
    return 0;
}

static void set_dart(int l, int i) {
    int *nl = nbuf + (size_t)l * NN;
    int p = perm[l][i], s = vol[l][i];
    for (int g = 0; g < G; g++) {
        int a = i * G + g;
        int b = (K + p) * G + gmul(g, s);
        nl[a] = b;
        nl[b] = a;
    }
}

static long dupcount(void) {
    long c = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (perm[l1][i] == perm[l2][i] && vol[l1][i] == vol[l2][i]) c++;
    return c;
}

static uint64_t full_mask(void) {
    return (1ULL << (2 * K)) - 1;
}

/* Sum over vertices of the number of block representatives NOT within distance D. */
static long unreached(void) {
    uint64_t *cur = rbuf1, *nxt = rbuf2;
    for (int x = 0; x < NN; x++) cur[x] = 0;
    for (int b = 0; b < 2 * K; b++) cur[b * G] = 1ULL << b;
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int x = 0; x < NN; x++) {
            uint64_t v = cur[x];
            for (int l = 0; l < d; l++) v |= cur[nbuf[(size_t)l * NN + x]];
            nxt[x] = v;
            changed |= (v != cur[x]);
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
        if (!changed) break;
    }
    long miss = 0;
    for (int x = 0; x < NN; x++) miss += 2 * K - __builtin_popcountll(cur[x]);
    reach_res = cur;
    return miss;
}

static long cost_now(void) {
    return unreached() + 1000L * dupcount();
}

/* Simulated annealing over permutations and voltages. Returns 1 when the lift is valid. */
static int lift_search(long iters, long patience) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) perm[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1), t = perm[l][i];
            perm[l][i] = perm[l][j];
            perm[l][j] = t;
        }
        for (int i = 0; i < K; i++) {
            vol[l][i] = rndint(G);
            set_dart(l, i);
        }
    }
    long cur = cost_now();
    long best = cur, last = 0;
    double c0 = cur > 1 ? (double)cur : 1.0;
    for (long t = 0; t < iters && cur != 0; t++) {
        if ((t & 31) == 0 && now() > lift_deadline) break;
        if (t - last > patience) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;
        if (K >= 2 && rnd01() < 0.25) {
            int l = rndint(d);
            int i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int t1 = perm[l][i1];
            perm[l][i1] = perm[l][i2];
            perm[l][i2] = t1;
            set_dart(l, i1);
            set_dart(l, i2);
            long c2 = cost_now();
            if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / temp)) {
                cur = c2;
            } else {
                t1 = perm[l][i1];
                perm[l][i1] = perm[l][i2];
                perm[l][i2] = t1;
                set_dart(l, i1);
                set_dart(l, i2);
            }
        } else {
            int l = rndint(d), i = rndint(K);
            if (reach_res && rnd01() < 0.4) {
                uint64_t full = full_mask();
                int x = -1;
                for (int tr = 0; tr < 30; tr++) {
                    int y = rndint(NN);
                    if (reach_res[y] != full) { x = y; break; }
                }
                if (x >= 0) {
                    int blk = x / G;
                    if (blk < K) {
                        i = blk;
                    } else {
                        int p = blk - K;
                        for (int q = 0; q < K; q++)
                            if (perm[l][q] == p) { i = q; break; }
                    }
                }
            }
            int old = vol[l][i];
            int nv = rndint(G);
            if (nv == old) continue;
            vol[l][i] = nv;
            set_dart(l, i);
            long c2 = cost_now();
            if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / temp)) {
                cur = c2;
            } else {
                vol[l][i] = old;
                set_dart(l, i);
            }
        }
        if (cur < best) { best = cur; last = t; }
    }
    return cur == 0;
}

static void lift_to_graph(Graph *g) {
    g->n = NN;
    for (int x = 0; x < NN; x++) {
        g->side[x] = (unsigned char)(x < K * G ? 0 : 1);
        g->deg[x] = d;
        for (int l = 0; l < d; l++) g->adj[x][l] = nbuf[(size_t)l * NN + x];
    }
}

static int pick_k(int kmax) {
    if (rnd01() < 0.2) return 1 + rndint(kmax);
    int bestk = 1;
    double bs = -1.0;
    for (int k = 1; k <= kmax; k++) {
        double s = (wins_[k] + 1.0) / (trials_[k] + 2.0) + 0.02 * rnd01();
        if (s > bs) { bs = s; bestk = k; }
    }
    return bestk;
}

static void lift_phase(double until) {
    lift_deadline = until;
    double goal = 1.05 * gbest.n;
    if (goal < 2.0 * d) goal = 2.0 * d;
    while (now() < until) {
        if (goal > MAXN - 2) goal = MAXN - 2;
        int k = pick_k(6);
        int target = (int)(goal / (2.0 * k)) + rndint(3);
        if (target < 2) target = 2;
        if (!choose_group(target)) { goal *= 0.99; continue; }
        K = k;
        NN = 2 * K * G;
        if (NN > MAXN) { goal *= 0.99; continue; }
        if (NN <= gbest.n) {
            double g2 = 1.02 * gbest.n;
            goal = goal > g2 ? goal : g2;
            continue;
        }
        trials_[k]++;
        if (lift_search(4000, 1200)) {
            wins_[k]++;
            lift_to_graph(&cand);
            if (is_valid(&cand) && cand.n > gbest.n) copy_graph(&gbest, &cand);
            double g2 = 1.04 * NN;
            goal = goal > g2 ? goal : g2;
        } else {
            double g2 = 1.02 * gbest.n;
            double g3 = goal * 0.99;
            goal = g2 > g3 ? g2 : g3;
        }
    }
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
    t_end = t0 + limit * 0.95 - 0.5;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || D < 2 || d > MAXD) { printf("0 0\n"); return 0; }
    read_start(&gbest);
    lift_phase(t0 + 0.7 * (t_end - t0));
    if (gbest.n > 0) grow_search(t_end);
    if (gbest.n == 0 || !is_valid(&gbest)) { printf("0 0\n"); return 0; }
    print_graph(&gbest);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Small exact constructions (kept for D = 3 and D = 4 calibration-style cases).
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

    total = max(1.0, 0.8 * time_limit - 2.0)
    final = t0 + total

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions.
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
    if D == 4 and time.monotonic() < final:
        try:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    consider(*_gq_w(q))
                    break
        except Exception:
            pass

    # Main search in C: lift search over semidirect products, then grow-by-two.
    remaining = final - time.monotonic() - 1.5
    if D >= 3 and d >= 3 and remaining > 3.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2)],
                             stdin_graph=best, timeout=remaining + 6.0)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
