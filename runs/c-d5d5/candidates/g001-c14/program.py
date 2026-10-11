"""Combined program: Python builds the best construction it can (PG(2,q), Araujo-Lopez,
W(q)), then the C engine searches from it.

C engine:
  1. Voltage lifts over semidirect products Z_m x| Z_k. Left multiplication by any group
     element is an automorphism, so diameter <= D is checked by BFS from the 2k orbit
     representatives only. Simulated annealing over voltages and base permutations.
  2. Grow by two: insert one vertex per side, then anneal degree-preserving edge swaps.
build() validates everything and keeps the best valid graph, so a failure costs only time.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core (combined engine).
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v" (a valid start graph), or "0 0".
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Phase 1: voltage lifts over Z_m x| Z_k (order N). Base: k vertices per side, d layers
 *          of random permutations, each dart (i, j, s) joins A_{i,x} to B_{j,x*s}.
 *          Left multiplication is an automorphism, so only the 2k orbit representatives
 *          need a BFS. Annealing over voltages and base permutations.
 * Phase 2: grow by two (insert one vertex per side, anneal degree-preserving swaps).
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
#define MAXK 4
#define MAXG 2048
#define BIGPEN 1000000L
#define TEMP_START 4.0
#define TEMP_END 0.1

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

typedef struct {
    int m, k, r;
    int rp[MAXG]; /* rp[b] = r^b mod m */
} Grp;

static int d, D;
static double t_end;

/* ------------------------------------------------------------------ utilities */

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

/* Largest possible order of a bipartite graph with max degree d and diameter D. */
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

/* ------------------------------------------------------------------ graph basics */

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

/* ------------------------------------------------------------------ full distance check */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

/* Number of unordered pairs at distance > D (0 means diameter <= D and connected). */
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

/* Simple, bipartite (by side labels), degree <= d, diameter <= D. */
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

/* ------------------------------------------------------------------ input / output */

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

/* K_{d,d}: valid for D >= 2. */
static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ------------------------------------------------------------------ groups */

/* Z_m x|_r Z_k: element (a, b) is the int a*k + b, (a,b)(c,e) = (a + r^b c, b + e). */
static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)(((long)a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
}

/* Uniform random (m, k, r) with m*k = N, gcd(r, m) = 1, r^k = 1 mod m. */
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
            if (rndint((int)count) == 0) { G->m = m; G->k = k; G->r = r; }
        }
    }
    if (!count) return 0;
    G->rp[0] = 1 % G->m;
    for (int b = 1; b < G->k; b++) G->rp[b] = (int)((long)G->rp[b - 1] * G->r % G->m);
    return 1;
}

/* ------------------------------------------------------------------ voltage lifts */

static int K_, NG, nd_;
static Grp GG;
static int Li[MAXK * MAXD], Lj[MAXK * MAXD], Lv[MAXK * MAXD];
static int LADJ[MAXN][MAXD];
static int LDEG[MAXN];
static int ldist[MAXN], lq[MAXN];

/* Unreached (representative, vertex) pairs over the 2K_ orbit representatives.
 * Zero means the lift has diameter <= D. Duplicate darts get a large penalty. */
static long lift_cost(void) {
    long pen = 0;
    for (int a = 0; a < nd_; a++)
        for (int b = a + 1; b < nd_; b++)
            if (Li[a] == Li[b] && Lj[a] == Lj[b] && Lv[a] == Lv[b]) pen += BIGPEN;
    if (pen) return pen;
    int N = NG, k = K_, n = 2 * k * N;
    memset(LDEG, 0, sizeof(int) * (size_t)n);
    for (int t = 0; t < nd_; t++) {
        int i = Li[t], j = Lj[t], s = Lv[t];
        for (int x = 0; x < N; x++) {
            int a = i * N + x, b = (k + j) * N + gmul(&GG, x, s);
            LADJ[a][LDEG[a]++] = b;
            LADJ[b][LDEG[b]++] = a;
        }
    }
    long cost = 0;
    for (int r = 0; r < 2 * k; r++) {
        int src = r * N; /* A_r for r < k, B_{r-k} for r >= k */
        for (int v = 0; v < n; v++) ldist[v] = -1;
        ldist[src] = 0;
        int h = 0, tl = 0, reached = 1;
        lq[tl++] = src;
        while (h < tl) {
            int u = lq[h++];
            if (ldist[u] >= D) continue;
            for (int e = 0; e < d; e++) {
                int w = LADJ[u][e];
                if (ldist[w] < 0) { ldist[w] = ldist[u] + 1; lq[tl++] = w; reached++; }
            }
        }
        cost += n - reached;
    }
    return cost;
}

/* Simulated annealing over voltages and in-layer base permutations. Returns final cost. */
static long anneal(long steps, double until) {
    long c = lift_cost();
    int sj[MAXK * MAXD], sv[MAXK * MAXD];
    for (long s = 0; s < steps && c > 0; s++) {
        if ((s & 127) == 0 && now() > until) break;
        memcpy(sj, Lj, sizeof(int) * (size_t)nd_);
        memcpy(sv, Lv, sizeof(int) * (size_t)nd_);
        if (K_ > 1 && rndint(10) < 2) {
            int l = rndint(d), a = rndint(K_), b = rndint(K_);
            int x = l * K_ + a, y = l * K_ + b;
            int tmp = Lj[x]; Lj[x] = Lj[y]; Lj[y] = tmp;
        } else {
            Lv[rndint(nd_)] = rndint(NG);
        }
        long c2 = lift_cost();
        double T = TEMP_START * pow(TEMP_END / TEMP_START, (double)s / (double)steps);
        if (c2 <= c || rnd01() < exp(-(double)(c2 - c) / T)) {
            c = c2;
        } else {
            memcpy(Lj, sj, sizeof(int) * (size_t)nd_);
            memcpy(Lv, sv, sizeof(int) * (size_t)nd_);
        }
    }
    return c;
}

/* One attempt: random base and voltages over group G, anneal. On success, improve best. */
static int lift_try(Graph *best, int k, int N, const Grp *G, long steps, double until) {
    K_ = k;
    NG = N;
    GG = *G;
    nd_ = k * d;
    for (int t = 0; t < d; t++) {
        int perm[MAXK];
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
        }
        for (int i = 0; i < k; i++) {
            Li[t * k + i] = i;
            Lj[t * k + i] = perm[i];
            Lv[t * k + i] = rndint(N);
        }
    }
    long c = anneal(steps, until);
    if (c != 0) return 0;

    static Graph cand;
    cand.n = 2 * k * N;
    for (int v = 0; v < cand.n; v++) {
        cand.deg[v] = 0;
        cand.side[v] = (unsigned char)(v >= k * N);
    }
    for (int t = 0; t < nd_; t++)
        for (int x = 0; x < N; x++)
            add_edge(&cand, Li[t] * N + x, (k + Lj[t]) * N + gmul(&GG, x, Lv[t]));
    if (cand.n > best->n && is_valid(&cand)) {
        copy_graph(best, &cand);
        return 1;
    }
    return 0;
}

static void lift_phase(Graph *best, double until) {
    static Grp G;
    long moore = moore_bound();
    int fails = 0;
    while (now() < until) {
        int r = rndint(20);
        int k = r < 6 ? 1 : r < 12 ? 2 : r < 17 ? 3 : 4;
        long N = (long)best->n / (2L * k) + 1 + rndint(2);
        if (N < 2 || 2L * k * N > moore || 2L * k * N > MAXN || N > MAXG) {
            if (++fails > 5000) return;
            continue;
        }
        for (int at = 0; at < 6 && now() < until; at++) {
            if (!random_group((int)N, &G)) break;
            if (lift_try(best, k, (int)N, &G, 40000, until)) break;
        }
    }
}

/* ------------------------------------------------------------------ grow by two */

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

/* ------------------------------------------------------------------ main */

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
    if (d < 1 || D < 1 || d > MAXD) { complete_bipartite(&best); print_graph(&best); return 0; }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);

    if (D >= 3 && d >= 2 && best.n < moore_bound()) {
        lift_phase(&best, t0 + (t_end - t0) * 0.7);
        grow_search(&best, t_end);
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


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


def _starts(d, D):
    """Constructions worth trying as start graphs (callables returning (n, edges))."""
    out = []
    if D >= 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                out.append(lambda q=q: lib.projective_plane_incidence(q))
                break
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            out.append(lambda: lib.araujo_lopez_graph(d - 2))
    if D >= 4 and 2 <= d - 1 <= 8 and lib.is_prime_power(d - 1):
        out.append(lambda: _gq_w(d - 1))
    return out


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d <= 0 or D <= 0:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]
    kdd = lib.haar_graph(d, range(d))          # K_{d,d}: valid for D >= 2
    if D == 2:
        return kdd                              # optimal for D = 2

    best = kdd
    for make in _starts(d, D):
        try:
            cand = make()
        except Exception:
            continue
        if cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
            best = cand

    if best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 3.0
    if budget < 2.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 10)
        n, e = lib.parse_graph_text(text)
    except Exception:
        return best
    if n > best[0] and lib.is_valid(n, e, d, D):
        best = (n, e)
    return best
