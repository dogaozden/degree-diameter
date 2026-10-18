"""Bi-Cayley / voltage-lift search with cheap annealing, then grow-by-two, with safe fallbacks.

Main change from the parent: the C engine no longer checks full diameter at every step.
A lift of a d-regular base multigraph (P vertices per side) over a group G of order N is
vertex-transitive on each fibre, so diameter <= D holds iff a BFS from one representative
per fibre reaches everything within D. The annealing objective is the number of such
far vertices, which costs O(P * P*N*d) per move instead of a full bitset check.
"""
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
#define MAXP 8
#define MAXDARTS (MAXP * MAXD)

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

/* ------------------------------------------------------------ full check */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

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

/* ------------------------------------------------------------ groups */

/* Z_m x|_r Z_k: element (a,b) is the int a*k+b; identity is 0. */
typedef struct {
    int m, k, r;
    int rp[MAXN];
} Grp;

static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)((a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
}

static int random_group(int N, Grp *G) {
    long count = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)(count < 2000000000L ? count : 2000000000L)) == 0) {
                G->m = m; G->k = k; G->r = r;
            }
        }
    }
    if (!count) return 0;
    G->rp[0] = 1 % G->m;
    for (int b = 1; b < G->k; b++) G->rp[b] = (int)((long)G->rp[b - 1] * G->r % G->m);
    return 1;
}

/* ------------------------------------------------------------ lift search state */

typedef struct { int i, j, g; } Dart;

static int P, NG, ND;
static Grp GG;
static Dart DT[MAXDARTS], DTold[MAXDARTS];
static int ladj[MAXN][MAXD];

/* Lift adjacency: A-vertex (i,x) = i*NG+x, B-vertex (j,y) = P*NG+j*NG+y.
 * Dart (i,j,g) joins (i,x) to (j, x*g) for all x in G. */
static void lift_adj(void) {
    int V = 2 * P * NG;
    int cnt[MAXN];
    memset(cnt, 0, sizeof(int) * (size_t)V);
    for (int t = 0; t < ND; t++) {
        int i = DT[t].i, j = DT[t].j, g = DT[t].g;
        for (int x = 0; x < NG; x++) {
            int u = i * NG + x;
            int w = P * NG + j * NG + gmul(&GG, x, g);
            ladj[u][cnt[u]++] = w;
            ladj[w][cnt[w]++] = u;
        }
    }
}

static int dist_[MAXN], que_[MAXN];

/* Number of vertices at distance > D from s in the lift (vertex-transitive on fibres). */
static int far_from(int s, int V) {
    for (int v = 0; v < V; v++) dist_[v] = -1;
    int h = 0, tl = 0;
    dist_[s] = 0;
    que_[tl++] = s;
    while (h < tl) {
        int v = que_[h++];
        if (dist_[v] >= D) continue;
        for (int k = 0; k < d; k++) {
            int u = ladj[v][k];
            if (dist_[u] < 0) { dist_[u] = dist_[v] + 1; que_[tl++] = u; }
        }
    }
    return V - tl;
}

/* Zero iff the lift has diameter <= D. Needs lift_adj() to be current. */
static long objective(void) {
    lift_adj();
    int V = 2 * P * NG;
    long f = 0;
    for (int i = 0; i < P; i++) f += far_from(i * NG, V);
    for (int j = 0; j < P; j++) f += far_from(P * NG + j * NG, V);
    return f;
}

static int dart_clash(int t) {
    for (int s = 0; s < ND; s++)
        if (s != t && DT[s].i == DT[t].i && DT[s].j == DT[t].j && DT[s].g == DT[t].g)
            return 1;
    return 0;
}

/* Random d-regular base with P vertices per side and distinct darts. */
static int init_darts(void) {
    int bj[MAXDARTS];
    ND = P * d;
    int c = 0;
    for (int j = 0; j < P; j++)
        for (int k = 0; k < d; k++) bj[c++] = j;
    for (int i = ND - 1; i > 0; i--) {
        int r = rndint(i + 1);
        int tmp = bj[i]; bj[i] = bj[r]; bj[r] = tmp;
    }
    for (int t = 0; t < ND; t++) {
        DT[t].i = t / d;
        DT[t].j = bj[t];
        int ok = 0;
        for (int tries = 0; tries < 10000 && !ok; tries++) {
            DT[t].g = rndint(NG);
            ok = 1;
            for (int s = 0; s < t; s++)
                if (DT[s].i == DT[t].i && DT[s].j == DT[t].j && DT[s].g == DT[t].g) { ok = 0; break; }
        }
        if (!ok) return 0;
    }
    return 1;
}

static void lift_to_graph(Graph *out) {
    int V = 2 * P * NG;
    out->n = V;
    for (int v = 0; v < V; v++) { out->deg[v] = 0; out->side[v] = v >= P * NG; }
    for (int u = 0; u < P * NG; u++)
        for (int k = 0; k < d; k++) add_edge(out, u, ladj[u][k]);
}

/* Simulated annealing over voltages and base partners. On success, out is the lift. */
static int anneal(Graph *out, long steps, double until) {
    if (!init_darts()) return 0;
    long f = objective();
    for (long s = 0; s < steps && f > 0; s++) {
        if ((s & 31) == 0 && now() > until) break;
        double T = 1.2 * (1.0 - (double)s / (double)steps) + 0.03;
        memcpy(DTold, DT, sizeof(Dart) * (size_t)ND);
        if (rnd01() < 0.7) {
            int t = rndint(ND);
            DT[t].g = rndint(NG);
            if (dart_clash(t)) { memcpy(DT, DTold, sizeof(Dart) * (size_t)ND); continue; }
        } else {
            int t = rndint(ND), q2 = rndint(ND);
            if (t == q2 || DT[t].j == DT[q2].j) continue;
            int tmp = DT[t].j; DT[t].j = DT[q2].j; DT[q2].j = tmp;
            if (dart_clash(t) || dart_clash(q2)) { memcpy(DT, DTold, sizeof(Dart) * (size_t)ND); continue; }
        }
        long nf = objective();
        if (nf <= f || rnd01() < exp((double)(f - nf) / T)) f = nf;
        else memcpy(DT, DTold, sizeof(Dart) * (size_t)ND);
    }
    if (f != 0) return 0;
    lift_adj();
    lift_to_graph(out);
    return 1;
}

static void lift_search(Graph *best, double until) {
    static Graph cand;
    long moore = moore_bound();
    static const int Ps[] = {1, 1, 2, 2, 3, 4, 6};
    int extra = 2, fails = 0;
    while (now() < until) {
        if (best->n >= moore) return;
        int bn = best->n > 2 * d ? best->n : 2 * d;
        P = Ps[rndint(7)];
        NG = bn / (2 * P) + 1 + rndint(extra + 1);
        if (NG < d) NG = d;
        if (2L * P * NG > moore || 2 * P * NG > MAXN) {
            if (++fails > 500) return;
            extra = 1;
            continue;
        }
        if (!random_group(NG, &GG)) continue;
        if (anneal(&cand, 2500, until) && cand.n > best->n && is_valid(&cand)) {
            copy_graph(best, &cand);
            extra = extra * 2 + 1;
            if (extra > 64) extra = 64;
        } else if (extra > 1) {
            extra /= 2;
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
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (D < 1 || d < 1 || d > MAXD) { printf("1 0\n"); return 0; }
    if (D == 1) { printf("2 1\n0 1\n"); return 0; }

    static Graph best;
    read_start(&best);
    if (best.n < moore_bound()) {
        lift_search(&best, t0 + (t_end - t0) * 0.8);
        if (best.n > 0) grow_search(&best, t_end);
    }
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def known_start(d, D):
    """Best graph Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)

    # Safe fallback chain: known construction, then K_{d,d}, then a single vertex.
    best = None
    for cand in (start, lib.haar_graph(d, range(d))):
        if cand is not None and lib.is_valid(cand[0], cand[1], d, D):
            best = cand
            break
    if best is None:
        best = (1, [])

    budget = 0.8 * time_limit - (time.monotonic() - t0) - 1.0
    if best[0] < lib.moore_bound(d, D) and budget > 0.5:
        try:
            stdin_graph = best if best[0] >= 2 else None
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=stdin_graph, timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass  # keep the valid fallback
    return best
