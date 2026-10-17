"""Combined search: exact Python starts for D = 3, then one C engine that runs
bi-Cayley lift search over semidirect groups (simulated annealing on voltages and
layer permutations, with a bandit over base sizes) and grow-by-two annealing."""
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a valid start graph, or "0 0".
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Phase 1 (lift search): bi-Cayley lifts over Z_m x|_r Z_k2. A base of k A-blocks and
 *   k B-blocks, d layers, each layer a permutation of blocks plus one voltage per block.
 *   Cost = unreached (representative, vertex) pairs + penalty * duplicate darts.
 *   Simulated annealing with stagnation restarts; bandit over k in 1..4.
 * Phase 2 (grow by two): insert one vertex per side, anneal degree-preserving swaps.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 12288
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXK 4
#define MAXK2 64
#define PENALTY 1000L

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;

/* ------------------------------------------------------------ utilities */

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
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

/* ------------------------------------------------------------ graph basics */

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

/* ------------------------------------------------------------ distance check */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

/* Unordered pairs at distance > D. Also fills badv[v] = number of far vertices from v. */
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
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN) return;
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

static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ------------------------------------------------------------ groups */

/* Z_m x|_r Z_k2: element (a, b) is the int a*k2 + b; (a,b)(c,e) = (a + r^b c, b + e). */
typedef struct {
    int m, k, r;
    int rp[MAXK2];
} Grp;
static Grp GR;

static int gmul(int x, int y) {
    int k = GR.k, m = GR.m;
    int a = x / k, b = x % k, c = y / k, e = y % k;
    return (int)(((long)a + (long)GR.rp[b] * c) % m) * k + (b + e) % k;
}

static int ginv(int x) {
    int k = GR.k, m = GR.m;
    int a = x / k, b = x % k;
    int nb = (k - b) % k;
    long c = (-((long)GR.rp[nb] * a)) % m;
    if (c < 0) c += m;
    return (int)c * k + nb;
}

static const int K2_CHOICES[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};

/* Sample Z_m x| Z_k2 with m*k2 >= target. Sets GR. Returns 1 on success. */
static int sample_group(long target) {
    for (int tries = 0; tries < 200; tries++) {
        int k2 = K2_CHOICES[rndint(20)];
        long m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        int r = -1;
        if (k2 == 1) r = 1;
        else if (k2 == 2 && rnd01() < 0.3) r = (int)(m - 1);
        else if (m <= 2) r = 1;
        else {
            for (int s = 0; s < 60; s++) {
                long c = 2 + rndint((int)(m - 2));
                if (gcd_i((int)c, (int)m) == 1 && powmod(c, k2, m) == 1 % m) { r = (int)c; break; }
            }
            if (r < 0) continue;
        }
        GR.m = (int)m;
        GR.k = k2;
        GR.r = r;
        GR.rp[0] = (int)(1 % m);
        for (int b = 1; b < k2; b++) GR.rp[b] = (int)((long)GR.rp[b - 1] * r % m);
        return 1;
    }
    return 0;
}

/* ------------------------------------------------------------ lifts */

/* Dart layer l, A-block i maps to B-block perm_[l][i] with voltage volt[l][i].
 * A vertex i*G+g ~ B vertex (k+j)*G + g*s, and B vertex (k+j)*G+h ~ i*G + h*s^{-1}. */
static int nbr[MAXD][MAXN];
static int perm_[MAXD][MAXK];
static int volt[MAXD][MAXK];
static int cur_k, cur_G, cur_N;
static uint32_t Rch[MAXN], Tch[MAXN];

static void set_dart(int l, int i) {
    int k = cur_k, G = cur_G;
    int j = perm_[l][i], s = volt[l][i];
    int si = ginv(s);
    for (int g = 0; g < G; g++) {
        nbr[l][i * G + g] = (k + j) * G + gmul(g, s);
        nbr[l][(k + j) * G + g] = i * G + gmul(g, si);
    }
}

/* Rch[v] bit b set when representative of block b is within distance D of v. */
static void compute_reach(void) {
    int N = cur_N, k = cur_k, G = cur_G;
    for (int v = 0; v < N; v++) Rch[v] = 0;
    for (int b = 0; b < 2 * k; b++) Rch[b * G] = 1u << b;
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint32_t x = Rch[v];
            for (int l = 0; l < d; l++) x |= Rch[nbr[l][v]];
            Tch[v] = x;
            changed |= (x != Rch[v]);
        }
        memcpy(Rch, Tch, sizeof(uint32_t) * (size_t)N);
        if (!changed) break;
    }
}

static int dupcount(void) {
    int c = 0;
    for (int i = 0; i < cur_k; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = 0; l2 < l; l2++)
                if (perm_[l][i] == perm_[l2][i] && volt[l][i] == volt[l2][i]) c++;
    return c;
}

static long eval_cost(void) {
    compute_reach();
    long tot = 0;
    for (int v = 0; v < cur_N; v++) tot += __builtin_popcount(Rch[v]);
    long unreached = (long)(2 * cur_k) * cur_N - tot;
    return unreached + PENALTY * (long)dupcount();
}

static int lift_trial(int k, int G, int iters, int patience, double deadline, Graph *out) {
    cur_k = k;
    cur_G = G;
    cur_N = 2 * k * G;
    int N = cur_N;
    uint32_t full = (1u << (2 * k)) - 1u;
    for (int l = 0; l < d; l++) {
        int p[MAXK];
        for (int i = 0; i < k; i++) p[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int s = p[i]; p[i] = p[j]; p[j] = s;
        }
        for (int i = 0; i < k; i++) {
            perm_[l][i] = p[i];
            volt[l][i] = rndint(G);
        }
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) set_dart(l, i);
    long cost = eval_cost();
    double c0 = cost > 1 ? (double)cost : 1.0;
    long best_cost = cost;
    long last = 0;
    for (long t = 0; t < iters && cost > 0; t++) {
        if ((t & 63) == 0 && now() > deadline) break;
        if (t - last > patience) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;

        if (k >= 2 && rnd01() < 0.25) {
            /* layer swap: exchange the targets of two A-blocks in one layer */
            int l = rndint(d);
            int i1 = rndint(k), i2 = rndint(k - 1);
            if (i2 >= i1) i2++;
            int tmp = perm_[l][i1]; perm_[l][i1] = perm_[l][i2]; perm_[l][i2] = tmp;
            set_dart(l, i1);
            set_dart(l, i2);
            long c2 = eval_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                if (cost < best_cost) { best_cost = cost; last = t; }
            } else {
                tmp = perm_[l][i1]; perm_[l][i1] = perm_[l][i2]; perm_[l][i2] = tmp;
                set_dart(l, i1);
                set_dart(l, i2);
            }
            continue;
        }

        /* voltage move: defect-targeted with probability 0.4 */
        int l = -1, i = -1;
        if (rnd01() < 0.4) {
            for (int s = 0; s < 20 && l < 0; s++) {
                int v = rndint(N);
                if (Rch[v] == full) continue;
                int blk = v / G;
                if (blk < k) {
                    i = blk;
                    l = rndint(d);
                } else {
                    int j = blk - k;
                    int ll = rndint(d);
                    int found = -1;
                    for (int q = 0; q < k; q++)
                        if (perm_[ll][q] == j) { found = q; break; }
                    if (found >= 0) { l = ll; i = found; }
                }
            }
        }
        if (l < 0) { l = rndint(d); i = rndint(k); }

        int old = volt[l][i];
        int ng = rndint(G);
        if (ng == old) continue;
        volt[l][i] = ng;
        set_dart(l, i);
        long c2 = eval_cost();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            if (cost < best_cost) { best_cost = cost; last = t; }
        } else {
            volt[l][i] = old;
            set_dart(l, i);
        }
    }
    if (cost != 0) return 0;

    out->n = N;
    for (int v = 0; v < N; v++) {
        out->deg[v] = 0;
        out->side[v] = (unsigned char)(v >= k * G);
    }
    for (int l = 0; l < d; l++)
        for (int u = 0; u < k * G; u++) add_edge(out, u, nbr[l][u]);
    return 1;
}

static void lift_search(Graph *best, double until) {
    static Graph cand;
    long moore = moore_bound();
    double wins[MAXK + 1], trials[MAXK + 1];
    for (int k = 0; k <= MAXK; k++) { wins[k] = 0; trials[k] = 0; }
    while (now() < until) {
        int k;
        if (rnd01() < 0.2) k = 1 + rndint(MAXK);
        else {
            double bestv = -1.0;
            k = 1;
            for (int kk = 1; kk <= MAXK; kk++) {
                double v = (wins[kk] + 1.0) / (trials[kk] + 2.0) + 0.02 * rnd01();
                if (v > bestv) { bestv = v; k = kk; }
            }
        }
        long base = best->n / (2 * k);
        long spread = base / 8 + 2;
        long target = base + 1 + rndint((int)spread);
        if (target < 2) target = 2;
        if (!sample_group(target)) continue;
        long G = (long)GR.m * GR.k;
        if (2L * k * G <= best->n || 2L * k * G > moore || 2L * k * G > MAXN) continue;
        trials[k] += 1.0;
        if (lift_trial(k, (int)G, 4000, 1200, until, &cand)) {
            wins[k] += 1.0;
            if (cand.n > best->n && is_valid(&cand)) copy_graph(best, &cand);
        }
    }
}

/* ------------------------------------------------------------ grow by two */

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
    static int used[MAXN];
    static int stamp = 0;
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

static void grow_search(Graph *best, double until) {
    static Graph work;
    while (now() < until && best->n + 2 <= moore_bound()) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(best, &work, now() + slice)) copy_graph(best, &work);
    }
}

/* ------------------------------------------------------------ main */

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
    t_end = t0 + limit * 0.95;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) { complete_bipartite(&best); print_graph(&best); return 0; }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);

    if (D >= 2 && best.n < moore_bound()) {
        double span = t_end - now();
        lift_search(&best, now() + 0.8 * span);
        grow_search(&best, t_end);
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _start_graph(d, D):
    """Best exact construction Python knows for (d, D), or None."""
    best = None
    if D >= 3:
        best = _best_pg(d)
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            al = lib.araujo_lopez_graph(d - 2)
            if best is None or al[0] > best[0]:
                best = al
        except ValueError:
            pass
    return best


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    st = _start_graph(d, D)
    if st is not None and st[0] > best[0] and lib.is_valid(st[0], st[1], d, D):
        best = st

    # Moore graphs cannot be beaten: return immediately (calibration case).
    if D == 3 and best[0] >= lib.moore_bound(d, D):
        return best

    budget = min(0.85 * time_limit - (time.monotonic() - t0) - 2.0, time_limit - 10.0)
    if budget >= 1.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=best, timeout=budget + 8.0)
            n, edges = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, edges, d, D):
                best = (n, edges)
        except (RuntimeError, ValueError):
            pass
    return best
