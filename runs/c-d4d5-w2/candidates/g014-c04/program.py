"""Bi-Cayley search over metacyclic and direct-product groups, plus grow-by-two annealing.

Changes from the parent:
- Replaces the voltage-lift stage with a bi-Cayley search. Vertices are (x,0) and (x,1) for x in a
  group G of order N, with (x,0) adjacent to (x*s,1) for s in a d-subset S of G. Left multiplication
  is an automorphism, so two BFS sources, (e,0) and (e,1), decide the diameter.
- Groups are random metacyclic groups Z_m x| Z_k, or direct products of two of them, of order N.
- Each order N gets a time slice of random-restart hill-climbing over S. The order grows until a
  slice fails, and each accepted graph is re-checked with lib-equivalent full validation in C.
- Start from the best algebraic graph (PG(2,q), W(q), Araujo-Pardo-Lopez, or K_{d,d}), with
  grow-by-two annealing on the remaining time as a fallback stage.
"""
import time

import itertools

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * 1. Bi-Cayley graphs over groups G of order N (metacyclic or direct products of metacyclic):
 *    vertices (x,0),(x,1); (x,0)~(x s,1) for s in S, |S| = d. The diameter is checked with two
 *    BFS sources, (e,0) and (e,1).
 * 2. Saturation of the start graph, and grow-by-two annealing on the remaining time.
 */
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
#define MAXG 128

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

typedef struct {
    int N;
    int mul[MAXG][MAXG];
    int inv[MAXG];
} Group;

static int d, D;
static double t_end;

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

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

/* Number of unordered pairs at distance > D; fills badv[v] = vertices at distance > D from v. */
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

/* Adding an A-B edge between vertices with spare degree never increases a distance. */
static int saturate(Graph *g) {
    int added = 0;
    for (int a = 0; a < g->n; a++) {
        if (g->side[a] != 0 || g->deg[a] >= d) continue;
        for (int b = 0; b < g->n && g->deg[a] < d; b++) {
            if (g->side[b] != 1 || g->deg[b] >= d || has_edge(g, a, b)) continue;
            add_edge(g, a, b);
            added++;
        }
    }
    return added;
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

/* ---------------------------------------------------------------- groups */

/* Z_m x|_r Z_k: element a*k + b, (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
static void fill_inv(Group *G) {
    for (int x = 0; x < G->N; x++)
        for (int y = 0; y < G->N; y++)
            if (G->mul[x][y] == 0) { G->inv[x] = y; break; }
}

static void fill_meta(Group *G, int m, int k, int r) {
    int N = m * k, rp[MAXG];
    G->N = N;
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            G->mul[x][y] = ((a + rp[b] * c) % m) * k + (b + e) % k;
        }
    }
    fill_inv(G);
}

/* Uniform random metacyclic group of order M (reservoir sampling over (m, k, r)). */
static int meta_pick(int M, int *om, int *ok, int *orr) {
    long count = 0;
    int found = 0;
    for (int m = 1; m <= M; m++) {
        if (M % m) continue;
        int k = M / m;
        if (m == 1) {
            count++;
            if (rndint((int)count) == 0) { *om = 1; *ok = k; *orr = 0; found = 1; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)count) == 0) { *om = m; *ok = k; *orr = r; found = 1; }
        }
    }
    return found;
}

static void fill_prod(Group *P, const Group *A, const Group *B) {
    int N2 = B->N;
    P->N = A->N * N2;
    for (int x = 0; x < P->N; x++) {
        int x1 = x / N2, x2 = x % N2;
        for (int y = 0; y < P->N; y++) {
            int y1 = y / N2, y2 = y % N2;
            P->mul[x][y] = A->mul[x1][y1] * N2 + B->mul[x2][y2];
        }
    }
    fill_inv(P);
}

/* Random group of order N: a metacyclic group, or a direct product of two metacyclic groups. */
static int pick_group(int N, Group *G) {
    static Group A, B;
    int m, k, r;
    if (N > MAXG || N < 2) return 0;
    int divs[MAXG], nd = 0;
    for (int f = 2; f < N; f++)
        if (N % f == 0) divs[nd++] = f;
    if (nd > 0 && rnd01() < 0.5) {
        int N1 = divs[rndint(nd)], N2 = N / N1;
        if (!meta_pick(N1, &m, &k, &r)) return 0;
        fill_meta(&A, m, k, r);
        if (!meta_pick(N2, &m, &k, &r)) return 0;
        fill_meta(&B, m, k, r);
        fill_prod(G, &A, &B);
    } else {
        if (!meta_pick(N, &m, &k, &r)) return 0;
        fill_meta(G, m, k, r);
    }
    return 1;
}

/* ------------------------------------------------------------ bi-Cayley */

static int bvis[2 * MAXG], bdist[2 * MAXG], bq[2 * MAXG];
static int bstamp = 0;

/* Vertices (x,0) = x and (x,1) = N + x; (x,0) ~ (x s,1), so (y,1) ~ (y s^-1, 0).
 * Left multiplication is an automorphism, so BFS from (e,0) and (e,1) decides the diameter. */
static long bi_bad(const Group *G, int N, const int *S) {
    long total = 0;
    for (int src = 0; src < 2; src++) {
        bstamp++;
        int head = 0, tail = 0, s0 = src * N;
        bvis[s0] = bstamp;
        bdist[s0] = 0;
        bq[tail++] = s0;
        while (head < tail) {
            int v = bq[head++], dv = bdist[v];
            if (dv >= D) continue;
            for (int i = 0; i < d; i++) {
                int u = v < N ? N + G->mul[v][S[i]] : G->mul[v - N][G->inv[S[i]]];
                if (bvis[u] != bstamp) {
                    bvis[u] = bstamp;
                    bdist[u] = dv + 1;
                    bq[tail++] = u;
                }
            }
        }
        total += 2L * N - tail;
    }
    return total;
}

static void build_bi(Graph *g, const Group *G, int N, const int *S) {
    g->n = 2 * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= N; }
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++) add_edge(g, x, N + G->mul[x][S[i]]);
}

static int in_set(const int *S, int k, int e) {
    for (int i = 0; i < k; i++)
        if (S[i] == e) return 1;
    return 0;
}

/* Random restarts plus hill-climbing on S: swap one element and accept if bad does not grow. */
static int bi_try(const Group *G, int N, int *S, int steps, double until) {
    for (int i = 0; i < d; i++) {
        int e;
        do { e = rndint(N); } while (in_set(S, i, e));
        S[i] = e;
    }
    long bad = bi_bad(G, N, S);
    for (int s = 0; s < steps && bad > 0; s++) {
        if ((s & 31) == 0 && now() > until) break;
        int i = rndint(d), old = S[i], e;
        do { e = rndint(N); } while (in_set(S, d, e));
        S[i] = e;
        long nb = bi_bad(G, N, S);
        if (nb <= bad || rnd01() < 0.02) bad = nb;
        else S[i] = old;
    }
    return bad == 0;
}

/* Search bi-Cayley graphs of order 2N with N increasing; each accepted graph is fully validated. */
static void bicayley_search(Graph *best, double until) {
    static Graph cand;
    static Group G;
    int S[MAXD];
    long moore = moore_bound();
    int N = best->n / 2 + 1;
    if (N < d + 1) N = d + 1;
    while (now() < until) {
        if (N > MAXG || 2L * N > moore || 2 * N > MAXN) break;
        double slice_end = now() + (until - now()) / 6.0;
        if (slice_end > until) slice_end = until;
        int ok = 0;
        while (!ok && now() < slice_end) {
            if (!pick_group(N, &G)) break;
            if (bi_try(&G, N, S, 400, slice_end)) {
                build_bi(&cand, &G, N, S);
                if (cand.n > best->n && is_valid(&cand)) {
                    copy_graph(best, &cand);
                    ok = 1;
                }
            }
        }
        N++;
    }
}

/* ------------------------------------------------------- grow by two */

static int pick_bad_vertex(const Graph *g) {
    static int list[MAXN];
    int c = 0;
    for (int v = 0; v < g->n; v++)
        if (badv[v] > 0) list[c++] = v;
    if (c == 0) return rndint(g->n);
    return list[rndint(c)];
}

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
        int v = pick_bad_vertex(work);
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
            bad_pairs(work);
        }
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    if (!is_valid(work)) return 0;
    saturate(work);
    return 1;
}

static void grow_search(Graph *best, double until) {
    static Graph work;
    while (now() < until && best->n + 2 <= moore_bound()) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(best, &work, now() + slice)) copy_graph(best, &work);
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
    t_end = t0 + limit * 0.93;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1) { printf("1 0\n"); return 0; }
    if (d > MAXD) { printf("1 0\n"); return 0; }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);

    saturate(&best);

    if (D >= 2 && best.n < moore_bound()) {
        bicayley_search(&best, t0 + (t_end - t0) * 0.7);
        if (best.n < moore_bound()) grow_search(&best, t_end);
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def _gq_w(q):
    """Incidence graph of points and lines of W(q): degree q+1, diameter 4."""
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


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def known_starts(d, D):
    """Algebraic candidates valid for diameter D (may be empty)."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
    if D >= 4:
        q = _largest_prime_power_le(min(d - 1, 9))
        if q is not None and q >= 2:
            out.append(_gq_w(q))
    return out


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.9 * time_limit - (time.monotonic() - t0) - 1.5
    if budget <= 0.2:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                         stdin_graph=best, timeout=budget + 4)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
