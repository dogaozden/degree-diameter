"""Combined program: bi-Cayley lift search in C (layer/voltage annealing over Z_m x| Z_k2),
then grow-by-two with edge-swap annealing in C. Python handles small exact cases and glue."""
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

#define MAXN 4096
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXK 4

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

static int gcd(int a, int b) {
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

static uint64_t BA[MAXN * MAXW], BB[MAXN * MAXW];
static int badv[MAXN];

static long bad_pairs(const Graph *g) {
    int n = g->n, W = (n + 63) / 64;
    uint64_t *cur = BA, *nxt = BB;
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

/* ------------------------------------------------------------ input / output */

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

/* ------------------------------------------------------------ bi-Cayley lifts
 * Group Z_GM x| Z_GK2, element a*GK2+b, (a,b)(c,e) = (a + r^b c, b+e).
 * Vertices: A-block i (i<K) is i*GO+g; B-block p is (K+p)*GO+h.
 * Layer l joins A-block i to B-block lay[l][i] by voltage S[l][i]:
 *   A_{i,g} ~ B_{p,g*s}. Left multiplication is an automorphism, so block
 *   representatives suffice for the diameter check. */

static int K, GO;
static int GM, GK2, GR;
static int rp[MAXN];
static int nbr[MAXD][MAXN];
static int lay[MAXD][MAXK];
static int S[MAXD][MAXK];
static unsigned char rA[MAXN], rB[MAXN];

static int gmul(int x, int y) {
    int a = x / GK2, b = x % GK2, c = y / GK2, e = y % GK2;
    return ((a + rp[b] * c) % GM) * GK2 + (b + e) % GK2;
}

static int sample_group(int target) {
    static const int K2S[24] = {1,1,2,2,2,3,3,4,4,5,6,6,7,8,9,10,12,14,16,18,20,24,30,36};
    for (int tries = 0; tries < 200; tries++) {
        int k2 = K2S[rndint(24)];
        int m = (target + k2 - 1) / k2 + rndint(2);
        if (m < 2) m = 2;
        int N = m * k2;
        if (N > MAXN || 2 * K * N > MAXN) continue;
        int r = 1;
        for (int rt = 0; rt < 60 && k2 > 1; rt++) {
            int c = (rt == 0) ? m - 1 : 1 + rndint(m - 1);
            if (c < 1) continue;
            if (gcd(c, m) != 1) continue;
            if (powmod(c, k2, m) != 1 % m) continue;
            r = c;
            break;
        }
        GM = m; GK2 = k2; GR = r; GO = N;
        rp[0] = 1 % m;
        for (int b = 1; b < k2; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
        return 1;
    }
    return 0;
}

static void set_dart(int l, int i, int p, int s) {
    for (int g = 0; g < GO; g++) {
        int a = i * GO + g;
        int b = (K + p) * GO + gmul(g, s);
        nbr[l][a] = b;
        nbr[l][b] = a;
    }
}

static int dupcount(void) {
    int c = 0;
    for (int l = 0; l < d; l++)
        for (int l2 = l + 1; l2 < d; l2++)
            for (int i = 0; i < K; i++)
                if (lay[l][i] == lay[l2][i] && S[l][i] == S[l2][i]) c++;
    return c;
}

/* Unreached (representative, vertex) pairs plus duplicate-edge penalty. Leaves the
 * reach masks of the current state in rA. */
static int eval_cost(void) {
    int NV = 2 * K * GO;
    unsigned char *cur = rA, *nxt = rB;
    memset(cur, 0, NV);
    for (int b = 0; b < 2 * K; b++) cur[b * GO] = (unsigned char)(1u << b);
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < NV; v++) {
            unsigned char x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nbr[l][v]];
            nxt[v] = x;
            if (x != cur[v]) changed = 1;
        }
        unsigned char *t = cur;
        cur = nxt;
        nxt = t;
        if (!changed) break;
    }
    if (cur != rA) memcpy(rA, cur, NV);
    int unre = 0;
    for (int v = 0; v < NV; v++) unre += 2 * K - __builtin_popcount(rA[v]);
    return unre + 1000 * dupcount();
}

static void random_state(void) {
    for (int l = 0; l < d; l++) {
        int perm[MAXK];
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < K; i++) lay[l][i] = perm[i];
        for (int i = 0; i < K; i++) S[l][i] = rndint(GO);
        for (int i = 0; i < K; i++) set_dart(l, i, lay[l][i], S[l][i]);
    }
}

static int sa_search(long iters, long patience, double deadline) {
    random_state();
    int NV = 2 * K * GO;
    int full = (1 << (2 * K)) - 1;
    int cost = eval_cost();
    double c0 = cost > 1 ? (double)cost : 1.0;
    int best = cost;
    long last = 0;
    for (long t = 0; t < iters; t++) {
        if (cost == 0) break;
        if (t - last > patience) break;
        if ((t & 31) == 0 && now() > deadline) break;
        double temp = 0.02 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.3) temp = 0.3;
        if (K >= 2 && rnd01() < 0.25) {
            int l = rndint(d);
            int i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int tmp = lay[l][i1]; lay[l][i1] = lay[l][i2]; lay[l][i2] = tmp;
            set_dart(l, i1, lay[l][i1], S[l][i1]);
            set_dart(l, i2, lay[l][i2], S[l][i2]);
            int c2 = eval_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
            } else {
                tmp = lay[l][i1]; lay[l][i1] = lay[l][i2]; lay[l][i2] = tmp;
                set_dart(l, i1, lay[l][i1], S[l][i1]);
                set_dart(l, i2, lay[l][i2], S[l][i2]);
            }
        } else {
            int l = rndint(d), i = rndint(K);
            if (rnd01() < 0.4) {
                for (int tr = 0; tr < 30; tr++) {
                    int v = rndint(NV);
                    if (rA[v] != full) {
                        int bv = v / GO;
                        if (bv < K) {
                            i = bv;
                        } else {
                            int p = bv - K;
                            for (int ii = 0; ii < K; ii++)
                                if (lay[l][ii] == p) { i = ii; break; }
                        }
                        break;
                    }
                }
            }
            int old = S[l][i];
            int nw = rndint(GO);
            if (nw == old) continue;
            S[l][i] = nw;
            set_dart(l, i, lay[l][i], nw);
            int c2 = eval_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
            } else {
                S[l][i] = old;
                set_dart(l, i, lay[l][i], old);
            }
        }
        if (cost < best) { best = cost; last = t; }
    }
    return cost == 0;
}

static int build_current(Graph *g) {
    int NA = K * GO, NV = 2 * NA;
    if (NV > MAXN) return 0;
    g->n = NV;
    for (int v = 0; v < NV; v++) { g->deg[v] = 0; g->side[v] = v >= NA; }
    for (int l = 0; l < d; l++)
        for (int a = 0; a < NA; a++) add_edge(g, a, nbr[l][a]);
    return is_valid(g);
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
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best, cand;
    if (d < 3 || d > 30 || D < 3) {
        read_start(&best);
        if (best.n == 0) {
            best.n = 2;
            best.deg[0] = best.deg[1] = 0;
            best.side[0] = 0;
            best.side[1] = 1;
            add_edge(&best, 0, 1);
        }
        print_graph(&best);
        return 0;
    }

    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    long moore = moore_bound();

    /* Phase A: bi-Cayley lift search, with a simple bandit over the base size k. */
    double phaseA_end = t0 + (t_end - t0) * 0.6;
    int trials[MAXK + 1] = {0}, wins[MAXK + 1] = {0};
    while (now() < phaseA_end && best.n < moore) {
        int k;
        if (rnd01() < 0.2) {
            k = 1 + rndint(MAXK);
        } else {
            double bs = -1.0;
            k = 1;
            for (int kk = 1; kk <= MAXK; kk++) {
                double sc = (wins[kk] + 1.0) / (trials[kk] + 2.0) + 0.05 * rnd01();
                if (sc > bs) { bs = sc; k = kk; }
            }
        }
        int base = best.n / (2 * k);
        int target = base + 1 + rndint(base / 8 + 2);
        K = k;
        if (!sample_group(target)) continue;
        if (2 * K * GO <= best.n || 2L * K * GO > moore) continue;
        trials[k]++;
        double dl = now() + 4.0;
        if (dl > phaseA_end) dl = phaseA_end;
        if (sa_search(8000, 2000, dl) && build_current(&cand) && cand.n > best.n) {
            copy_graph(&best, &cand);
            wins[k]++;
        }
    }

    /* Phase B: grow by two from the best graph. */
    if (best.n < moore) grow_search(&best, t_end);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def known_start(d, D):
    """Best exact construction Python builds directly for D = 3, or None."""
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    best = lib.haar_graph(d, range(d))   # K_{d,d}: always valid for D >= 2
    if D == 2 or d > 30:
        return best

    def consider(cand):
        nonlocal best
        if cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
            best = (cand[0], list(cand[1]))

    if D == 3 and lib.is_prime_power(d - 1):
        consider(lib.projective_plane_incidence(d - 1))   # Moore graph: optimal
        return best

    s = known_start(d, D)
    if s is not None:
        consider(s)

    budget = min(0.85 * time_limit, time_limit - 6.0) - (time.monotonic() - t0) - 1.0
    if budget < 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 8.0)
        consider(lib.parse_graph_text(text))
    except Exception:
        pass   # keep the valid fallback
    return best
