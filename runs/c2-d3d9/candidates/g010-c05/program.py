"""Cayley-first search for bipartite degree-diameter graphs.

Changed from the parent: the C engine now starts with an EXHAUSTIVE scan of abelian
bipartite Cayley graphs (every group Z_m x Z_k with m | k, every connection set
{e, a, b} for d = 3, or {e, a} for d = 2) over a growing order N. A hit at order N
gives 2N vertices. The random metacyclic hill-climb (a non-abelian Cayley family)
follows, then growth by two vertices. Python keeps the valid fallback and checks
every result with lib.is_valid.
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

#define MAXV 2048
#define MAXG 1024
#define MAXD 16
#define MAXW (MAXV / 64)

typedef struct {
    int n;
    int deg[MAXV];
    int adj[MAXV][MAXD];
    unsigned char side[MAXV];
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

static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ------------------------------------------------------------ diameter check */

static uint64_t RA[MAXV * MAXW], RB[MAXV * MAXW];
static int badv[MAXV];

/* Number of unordered pairs at distance > D. */
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
    if (g->n <= 0 || g->n > MAXV) return 0;
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
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXV) return;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n ||
            g->deg[u] >= MAXD || g->deg[v] >= MAXD) { g->n = 0; return; }
        add_edge(g, u, v);
    }
    static int queue[MAXV];
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

/* ------------------------------------------------------------ groups and Cayley graphs */

/* Group Z_m x|_r Z_k, element (a,b) = a*k+b, (a,b)(c,e) = (a + r^b c mod m, b+e mod k).
 * r = 1 gives the direct product Z_m x Z_k. */
static int gN = 0;
static int gmt[MAXG * MAXG];
static int ginvt[MAXG];
static int rpw[MAXG];
static int cdist[2 * MAXG], cq[2 * MAXG];

static void build_group(int m, int k, int r) {
    int N = m * k;
    gN = N;
    for (int b = 0; b < k; b++) rpw[b] = (int)powmod(r, b, m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            gmt[x * N + y] = (int)((((long)a + (long)rpw[b] * c) % m) * k + (b + e) % k);
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (gmt[x * N + y] == 0) { ginvt[x] = y; break; }
}

/* Bipartite Cayley graph: A_x ~ B_{x s_i}. Left multiplication is transitive on each side,
 * so BFS from A_e and B_e decides the diameter. Returns the number of vertices missed. */
static long cay_cost(const int *s, int dd) {
    int N = gN, V = 2 * N;
    int si[MAXD];
    for (int i = 0; i < dd; i++) si[i] = ginvt[s[i]];
    long miss = 0;
    for (int src = 0; src < 2; src++) {
        for (int v = 0; v < V; v++) cdist[v] = -1;
        int head = 0, tail = 0, s0 = src ? N : 0;
        cdist[s0] = 0;
        cq[tail++] = s0;
        while (head < tail) {
            int v = cq[head++];
            if (cdist[v] >= D) continue;
            if (v < N) {
                for (int i = 0; i < dd; i++) {
                    int u = N + gmt[v * N + s[i]];
                    if (cdist[u] < 0) { cdist[u] = cdist[v] + 1; cq[tail++] = u; }
                }
            } else {
                int y = v - N;
                for (int i = 0; i < dd; i++) {
                    int u = gmt[y * N + si[i]];
                    if (cdist[u] < 0) { cdist[u] = cdist[v] + 1; cq[tail++] = u; }
                }
            }
        }
        miss += V - tail;
    }
    return miss;
}

static int make_candidate(Graph *g, int N, const int *s, int dd) {
    g->n = 2 * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= N; }
    for (int x = 0; x < N; x++)
        for (int i = 0; i < dd; i++) add_edge(g, x, N + gmt[x * N + s[i]]);
    return is_valid(g);
}

/* s[0] = e, s[1..dd-1] distinct and non-identity. Requires N >= dd + 1. */
static void random_set(int N, int dd, int *s) {
    s[0] = 0;
    for (int i = 1; i < dd; i++) {
        int x, dup;
        do {
            x = 1 + rndint(N - 1);
            dup = 0;
            for (int j = 0; j < i; j++) if (s[j] == x) { dup = 1; break; }
        } while (dup);
        s[i] = x;
    }
}

static void random_change(int N, int dd, int *s, int i) {
    int x, dup;
    do {
        x = 1 + rndint(N - 1);
        dup = 0;
        for (int j = 0; j < dd; j++) if (s[j] == x) { dup = 1; break; }
    } while (dup);
    s[i] = x;
}

/* Phase 1: exhaustive scan over abelian groups Z_m x Z_k (m | k), with orders N ascending.
 * For d = 3 every set {e, a, b} is tried; for d = 2 every {e, a}; otherwise random sets. */
static void abelian_phase(Graph *best, double until) {
    if (d < 2) return;
    long hi = moore_bound() / 2;
    if (hi > MAXG) hi = MAXG;
    int lo = best->n / 2 + 1;
    if (lo < d + 1) lo = d + 1;
    static Graph cand;
    int s[MAXD];
    for (int N = lo; N <= hi; N++) {
        if (now() > until) return;
        int done = 0;
        for (int m = 1; m * m <= N && !done; m++) {
            if (N % m) continue;
            int k = N / m;
            if (k % m) continue;
            build_group(m, k, 1);
            if (d == 2) {
                s[0] = 0;
                for (int a = 1; a < N && !done; a++) {
                    s[1] = a;
                    if (cay_cost(s, 2) == 0 && make_candidate(&cand, N, s, 2) && cand.n > best->n) {
                        copy_graph(best, &cand);
                        done = 1;
                    }
                }
            } else if (d == 3) {
                s[0] = 0;
                for (int a = 1; a < N && !done; a++) {
                    if (now() > until) return;
                    for (int b = a + 1; b < N; b++) {
                        s[1] = a;
                        s[2] = b;
                        if (cay_cost(s, 3) == 0 && make_candidate(&cand, N, s, 3) && cand.n > best->n) {
                            copy_graph(best, &cand);
                            done = 1;
                            break;
                        }
                    }
                }
            } else {
                for (int t = 0; t < 4000 && !done; t++) {
                    if ((t & 63) == 0 && now() > until) return;
                    random_set(N, d, s);
                    if (cay_cost(s, d) == 0 && make_candidate(&cand, N, s, d) && cand.n > best->n) {
                        copy_graph(best, &cand);
                        done = 1;
                    }
                }
            }
        }
    }
}

/* Phase 2: metacyclic (possibly non-abelian) groups near the current order, hill-climbed. */
static int cgm[4096], cgk[4096], cgr[4096];

static void meta_phase(Graph *best, double until) {
    if (d < 2) return;
    static Graph cand;
    int s[MAXD];
    long hi = moore_bound() / 2;
    if (hi > MAXG) hi = MAXG;
    while (now() < until) {
        int lo = best->n / 2 + 1;
        if (lo < d + 1) lo = d + 1;
        if (lo > hi) return;
        int N = lo + rndint(12);
        if (N > hi) N = (int)(lo + rndint((int)(hi - lo + 1)));
        int G = 0;
        for (int m = 1; m <= N; m++) {
            if (N % m) continue;
            int k = N / m;
            if (m == 1) {
                if (G < 4096) { cgm[G] = 1; cgk[G] = k; cgr[G] = 0; G++; }
                continue;
            }
            for (int r = 1; r < m; r++) {
                if (gcd(r, m) != 1 || powmod(r, k, m) != 1 % m) continue;
                if (G < 4096) { cgm[G] = m; cgk[G] = k; cgr[G] = r; G++; }
            }
        }
        if (G == 0) continue;
        int gi = rndint(G);
        build_group(cgm[gi], cgk[gi], cgr[gi]);
        for (int rep = 0; rep < 3 && now() < until; rep++) {
            random_set(N, d, s);
            long cur = cay_cost(s, d);
            for (int st = 0; st < 6000 && cur > 0; st++) {
                if ((st & 127) == 0 && now() > until) break;
                int i = 1 + rndint(d - 1);
                int old = s[i];
                random_change(N, d, s, i);
                long c = cay_cost(s, d);
                if (c <= cur || rnd01() < 0.02) cur = c;
                else s[i] = old;
            }
            if (cur == 0 && make_candidate(&cand, N, s, d) && cand.n > best->n) {
                copy_graph(best, &cand);
                break;
            }
        }
    }
}

/* ------------------------------------------------------------ grow by two */

static int grow_once(const Graph *best, Graph *work, double until) {
    int n = best->n;
    if (n + 2 > moore_bound() || n + 2 > MAXV) return 0;
    copy_graph(work, best);
    int x = n, y = n + 1;
    work->n = n + 2;
    work->deg[x] = work->deg[y] = 0;
    work->side[x] = 0;
    work->side[y] = 1;
    add_edge(work, x, y);
    static int used[MAXV];
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
    while (now() < until && best->n + 2 <= moore_bound() && best->n + 2 <= MAXV) {
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

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) {
        best.n = 1;
        best.deg[0] = 0;
        best.side[0] = 0;
        print_graph(&best);
        return 0;
    }
    if (D == 1) {
        best.n = 2;
        best.deg[0] = best.deg[1] = 0;
        best.side[0] = 0;
        best.side[1] = 1;
        add_edge(&best, 0, 1);
        print_graph(&best);
        return 0;
    }

    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);

    if (best.n < moore_bound()) {
        double span = t_end - t0;
        abelian_phase(&best, t0 + span * 0.55);
        meta_phase(&best, t0 + span * 0.80);
        if (d >= 2) grow_search(&best, t_end);
    }
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


def fallback(d, D):
    """Always-valid simple graph: K_{d,d} for D >= 2, a single edge for D = 1."""
    if D >= 2 and d >= 1:
        return lib.haar_graph(d, range(d))
    if D >= 1 and d >= 1:
        return (2, [(0, 1)])
    return (1, [])


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    if start is not None and not lib.is_valid(*start, d, D):
        start = None
    best = start if start is not None else fallback(d, D)
    if not lib.is_valid(*best, d, D):
        best = (1, [])

    # Reserve time for the one-off C compile (it happens inside run_c).
    budget = 0.8 * time_limit - (time.monotonic() - t0) - 3.0
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # Moore graph already: just exercise the engine

    if budget > 0.3:
        try:
            stdin_graph = best if best[0] >= 2 else None
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=stdin_graph, timeout=budget + 2.0)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(*out, d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
