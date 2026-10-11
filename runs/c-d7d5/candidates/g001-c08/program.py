"""Search for large bipartite graphs of max degree d and diameter <= D.

New in this version: a C engine that searches bi-Cayley lifts over semidirect
products Z_M x| Z_K2 (K2 divides the order, K2 <= 36) with k base vertices per
side. Each of the d layers is a permutation of the k base vertices plus one
group voltage per dart. Simulated annealing minimises the number of unreached
(representative, vertex) pairs. Two move types are used: re-voltage one dart,
and swap two targets inside one layer. Both keep every vertex at degree d.
Representatives are enough because left multiplication is an automorphism.
The C engine also validates any start graph it receives and keeps the best
valid graph it has seen. Timing uses wall-clock time.
"""
import itertools
import time

import lib


C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 200000
#define MAXORDER 1500

static int gd = 3, gD = 3;
static double budget = 10.0;
static double t_begin = 0.0;
static uint64_t rs = 0x9E3779B97F4A7C15ULL;

static double wall(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
}
static double elapsed(void) { return wall() - t_begin; }
static int time_up(void) { return elapsed() >= budget; }

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int n) {
    if (n <= 1) return 0;
    return (int)(rnd64() % (uint64_t)n);
}
static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

/* ---------------------------------------------------------------- validation */

static int cmp_u64(const void *a, const void *b) {
    uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b;
    return (x > y) - (x < y);
}

/* 1 iff simple, bipartite, max degree <= gd, diameter <= gD, connected. */
static int graph_valid(int n, int m, const int *eu, const int *ev) {
    if (n < 1 || n > MAXN || m < 0) return 0;
    int ok = 1;
    uint64_t *keys = malloc(sizeof(uint64_t) * (size_t)(m > 0 ? m : 1));
    int *deg = calloc((size_t)n, sizeof(int));
    int *off = malloc(sizeof(int) * (size_t)(n + 1));
    int *fill = malloc(sizeof(int) * (size_t)n);
    int *color = malloc(sizeof(int) * (size_t)n);
    int *queue = malloc(sizeof(int) * (size_t)n);
    int *dist = malloc(sizeof(int) * (size_t)n);
    int *adj = malloc(sizeof(int) * (size_t)(2 * m + 1));

    for (int i = 0; i < m; i++) {
        int u = eu[i], v = ev[i];
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) { ok = 0; break; }
        if (u > v) { int t = u; u = v; v = t; }
        keys[i] = (uint64_t)u * (uint64_t)n + (uint64_t)v;
        deg[u]++;
        deg[v]++;
    }
    if (ok) {
        qsort(keys, (size_t)m, sizeof(uint64_t), cmp_u64);
        for (int i = 1; i < m; i++) {
            if (keys[i] == keys[i - 1]) { ok = 0; break; }
        }
    }
    for (int i = 0; ok && i < n; i++) {
        if (deg[i] > gd) ok = 0;
    }
    if (ok) {
        off[0] = 0;
        for (int i = 0; i < n; i++) {
            off[i + 1] = off[i] + deg[i];
            fill[i] = off[i];
        }
        for (int i = 0; i < m; i++) {
            int u = eu[i], v = ev[i];
            adj[fill[u]++] = v;
            adj[fill[v]++] = u;
        }
        for (int i = 0; i < n; i++) color[i] = -1;
        for (int s = 0; s < n && ok; s++) {
            if (color[s] != -1) continue;
            int qh = 0, qt = 0;
            color[s] = 0;
            queue[qt++] = s;
            while (qh < qt && ok) {
                int u = queue[qh++];
                for (int p = off[u]; p < off[u + 1]; p++) {
                    int v = adj[p];
                    if (color[v] == -1) {
                        color[v] = 1 - color[u];
                        queue[qt++] = v;
                    } else if (color[v] == color[u]) {
                        ok = 0;
                        break;
                    }
                }
            }
        }
    }
    if (ok) {
        for (int s = 0; s < n && ok; s++) {
            for (int i = 0; i < n; i++) dist[i] = -1;
            int qh = 0, qt = 0;
            dist[s] = 0;
            queue[qt++] = s;
            while (qh < qt) {
                int u = queue[qh++];
                if (dist[u] >= gD) continue;
                for (int p = off[u]; p < off[u + 1]; p++) {
                    int v = adj[p];
                    if (dist[v] < 0) {
                        dist[v] = dist[u] + 1;
                        queue[qt++] = v;
                    }
                }
            }
            if (qt != n) ok = 0;
        }
    }
    free(keys); free(deg); free(off); free(fill);
    free(color); free(queue); free(dist); free(adj);
    return ok;
}

/* ------------------------------------------------------------- best storage */

static int best_n = 0, best_m = 0;
static int *best_eu = NULL, *best_ev = NULL;

static void offer(int n, int m, const int *eu, const int *ev) {
    if (n <= best_n) return;
    if (!graph_valid(n, m, eu, ev)) return;
    int *a = malloc(sizeof(int) * (size_t)(m > 0 ? m : 1));
    int *b = malloc(sizeof(int) * (size_t)(m > 0 ? m : 1));
    if (m > 0) {
        memcpy(a, eu, sizeof(int) * (size_t)m);
        memcpy(b, ev, sizeof(int) * (size_t)m);
    }
    free(best_eu);
    free(best_ev);
    best_eu = a;
    best_ev = b;
    best_n = n;
    best_m = m;
}

static void read_start(void) {
    long n = 0, m = 0;
    if (scanf("%ld %ld", &n, &m) != 2) return;
    if (n <= 0 || m < 0 || n > MAXN || m > 5000000L) return;
    int *eu = malloc(sizeof(int) * (size_t)(m > 0 ? m : 1));
    int *ev = malloc(sizeof(int) * (size_t)(m > 0 ? m : 1));
    int good = 1;
    for (long i = 0; i < m; i++) {
        long u, v;
        if (scanf("%ld %ld", &u, &v) != 2) { good = 0; break; }
        eu[i] = (int)u;
        ev[i] = (int)v;
    }
    if (good) offer((int)n, (int)m, eu, ev);
    free(eu);
    free(ev);
}

/* ------------------------------------------------------------------ groups */

typedef struct {
    int G, K2, M;
    int *mt;   /* mt[x*G+y] = x*y */
    int *inv;  /* inv[x] */
} Group;

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int powmod_i(int b, int e, int m) {
    long long r = 1 % m, x = b % m;
    while (e > 0) {
        if (e & 1) r = (r * x) % m;
        x = (x * x) % m;
        e >>= 1;
    }
    return (int)r;
}

/* Z_M x| Z_K2, element (a,b) coded as a*K2+b, (a,b)(c,d) = (a + r^b c, b + d). */
static void group_build(Group *g, int M, int K2, int r) {
    int G = M * K2;
    g->G = G; g->K2 = K2; g->M = M;
    int *pw = malloc(sizeof(int) * (size_t)K2);
    for (int b = 0; b < K2; b++) pw[b] = powmod_i(r, b, M);
    g->mt = malloc(sizeof(int) * (size_t)G * (size_t)G);
    g->inv = malloc(sizeof(int) * (size_t)G);
    for (int x = 0; x < G; x++) {
        int a1 = x / K2, b1 = x % K2;
        for (int y = 0; y < G; y++) {
            int a2 = y / K2, b2 = y % K2;
            long long a = ((long long)a1 + (long long)pw[b1] * a2) % M;
            int b = (b1 + b2) % K2;
            g->mt[(size_t)x * G + y] = (int)a * K2 + b;
        }
    }
    for (int x = 0; x < G; x++) {
        g->inv[x] = 0;
        for (int y = 0; y < G; y++) {
            if (g->mt[(size_t)x * G + y] == 0) { g->inv[x] = y; break; }
        }
    }
    free(pw);
}

static void group_free(Group *g) {
    free(g->mt);
    free(g->inv);
}

/* ------------------------------------------------------------------- lifts */

typedef struct {
    int k, d, G, N;
    Group *g;
    int *tj;   /* tj[t]: target base of dart t, t = l*k + i */
    int *sv;   /* voltage of dart t */
    int *ip;   /* ip[l*k+j]: base i with tj[l*k+i] == j */
    int *stj, *ssv, *sip;
    int *vis, *q;
    int gen;
} Lift;

static void lift_alloc(Lift *L, int k, int d, Group *g) {
    int dk = d * k;
    L->k = k;
    L->d = d;
    L->G = g->G;
    L->N = 2 * k * g->G;
    L->g = g;
    L->tj = malloc(sizeof(int) * (size_t)dk);
    L->sv = malloc(sizeof(int) * (size_t)dk);
    L->ip = malloc(sizeof(int) * (size_t)dk);
    L->stj = malloc(sizeof(int) * (size_t)dk);
    L->ssv = malloc(sizeof(int) * (size_t)dk);
    L->sip = malloc(sizeof(int) * (size_t)dk);
    L->vis = calloc((size_t)L->N, sizeof(int));
    L->q = malloc(sizeof(int) * (size_t)L->N);
    L->gen = 0;
}

static void lift_free(Lift *L) {
    free(L->tj); free(L->sv); free(L->ip);
    free(L->stj); free(L->ssv); free(L->sip);
    free(L->vis); free(L->q);
}

/* Vertices: A(i,g) = i*G+g, B(j,h) = (k+j)*G+h.
   Dart t = (layer l, base i): A(i,g) -- B(tj[t], g*sv[t]). */
static void lift_random(Lift *L) {
    int k = L->k, d = L->d, G = L->G;
    int perm[16];
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < k; i++) {
            L->tj[l * k + i] = perm[i];
            L->ip[l * k + perm[i]] = i;
            L->sv[l * k + i] = rndint(G);
        }
    }
}

/* Number of vertices within distance gD of src. */
static int bfs_reach(Lift *L, int src) {
    const int k = L->k, d = L->d, G = L->G, kG = k * G;
    const int *mt = L->g->mt, *inv = L->g->inv;
    const int *tj = L->tj, *sv = L->sv, *ip = L->ip;
    int *vis = L->vis, *q = L->q;
    if (L->gen >= 2000000000) {
        memset(vis, 0, sizeof(int) * (size_t)L->N);
        L->gen = 0;
    }
    int gen = ++L->gen;
    int qh = 0, qt = 0;
    q[qt++] = src;
    vis[src] = gen;
    for (int lev = 0; lev < gD && qh < qt; lev++) {
        int end = qt;
        for (; qh < end; qh++) {
            int v = q[qh];
            if (v < kG) {
                int i = v / G, g = v - i * G;
                for (int l = 0; l < d; l++) {
                    int t = l * k + i;
                    int w = (k + tj[t]) * G + mt[g * G + sv[t]];
                    if (vis[w] != gen) { vis[w] = gen; q[qt++] = w; }
                }
            } else {
                int b = v - kG;
                int j = b / G, h = b - j * G;
                for (int l = 0; l < d; l++) {
                    int i = ip[l * k + j];
                    int t = l * k + i;
                    int w = i * G + mt[h * G + inv[sv[t]]];
                    if (vis[w] != gen) { vis[w] = gen; q[qt++] = w; }
                }
            }
        }
    }
    return qt;
}

/* Sum over the 2k representatives of unreached vertices. Zero means valid. */
static int lift_cost(Lift *L) {
    int k = L->k, G = L->G, N = L->N;
    int total = 0;
    for (int i = 0; i < k; i++) total += N - bfs_reach(L, i * G);
    for (int j = 0; j < k; j++) total += N - bfs_reach(L, (k + j) * G);
    return total;
}

static void lift_move(Lift *L) {
    int k = L->k, d = L->d, G = L->G;
    if (k >= 2 && rnd01() < 0.4) {
        int l = rndint(d);
        int i1 = rndint(k), i2 = rndint(k - 1);
        if (i2 >= i1) i2++;
        int t1 = l * k + i1, t2 = l * k + i2;
        int tmp = L->tj[t1];
        L->tj[t1] = L->tj[t2];
        L->tj[t2] = tmp;
        for (int i = 0; i < k; i++) L->ip[l * k + L->tj[l * k + i]] = i;
    } else {
        int t = rndint(d * k);
        L->sv[t] = rndint(G);
    }
}

/* Simulated annealing on the cost. Returns the final cost. */
static int lift_anneal(Lift *L, int steps, double T0) {
    int dk = L->d * L->k;
    int cur = lift_cost(L);
    for (int s = 0; s < steps && cur > 0; s++) {
        if ((s & 127) == 0 && time_up()) break;
        memcpy(L->stj, L->tj, sizeof(int) * (size_t)dk);
        memcpy(L->ssv, L->sv, sizeof(int) * (size_t)dk);
        memcpy(L->sip, L->ip, sizeof(int) * (size_t)dk);
        lift_move(L);
        int c2 = lift_cost(L);
        int delta = c2 - cur;
        double T = T0 * (1.0 - (double)s / (double)steps) + 0.02;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = c2;
        } else {
            memcpy(L->tj, L->stj, sizeof(int) * (size_t)dk);
            memcpy(L->sv, L->ssv, sizeof(int) * (size_t)dk);
            memcpy(L->ip, L->sip, sizeof(int) * (size_t)dk);
        }
    }
    return cur;
}

/* Emit the lift as a simple graph and offer it. */
static void emit_lift(const Lift *L) {
    int k = L->k, d = L->d, G = L->G, N = L->N;
    size_t cap = (size_t)d * (size_t)k * (size_t)G;
    uint64_t *keys = malloc(sizeof(uint64_t) * (cap > 0 ? cap : 1));
    size_t m = 0;
    for (int t = 0; t < d * k; t++) {
        int i = t % k, j = L->tj[t];
        for (int g = 0; g < G; g++) {
            int a = i * G + g;
            int b = (k + j) * G + L->g->mt[g * G + L->sv[t]];
            keys[m++] = (uint64_t)a * (uint64_t)N + (uint64_t)b;
        }
    }
    qsort(keys, m, sizeof(uint64_t), cmp_u64);
    size_t u = 0;
    for (size_t x = 0; x < m; x++) {
        if (x == 0 || keys[x] != keys[x - 1]) keys[u++] = keys[x];
    }
    int *eu = malloc(sizeof(int) * (u > 0 ? u : 1));
    int *ev = malloc(sizeof(int) * (u > 0 ? u : 1));
    for (size_t x = 0; x < u; x++) {
        eu[x] = (int)(keys[x] / (uint64_t)N);
        ev[x] = (int)(keys[x] % (uint64_t)N);
    }
    offer(N, (int)u, eu, ev);
    free(eu);
    free(ev);
    free(keys);
}

/* ------------------------------------------------------------------- main */

static const int kpool[6] = {1, 1, 2, 2, 3, 4};
static const int dpool[23] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16,
                              18, 20, 21, 24, 28, 30, 35, 36, 40};

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed budget_seconds\n");
        return 1;
    }
    gd = atoi(argv[1]);
    gD = atoi(argv[2]);
    uint64_t seed = (uint64_t)strtoull(argv[3], NULL, 10);
    budget = atof(argv[4]);
    rs ^= seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd64();
    t_begin = wall();

    read_start();

    if (gd >= 1 && gD >= 1) {
        while (!time_up()) {
            int k = kpool[rndint(6)];
            int lo = best_n / (2 * k) + 1;
            int spread = lo / 25;
            if (spread < 2) spread = 2;
            int G = lo + rndint(spread);
            if (G < 1 || G > MAXORDER || 2 * k * G > MAXN) continue;

            int cands[32], nc = 0;
            for (int c = 0; c < 23; c++) {
                if (G % dpool[c] == 0) cands[nc++] = dpool[c];
            }
            int K2 = cands[rndint(nc)];
            int M = G / K2;
            int r = 0;
            if (M > 1 && K2 > 1) {
                int found = 0;
                for (int tries = 0; tries < 200 && !found; tries++) {
                    int c = (tries == 0) ? M - 1 : 1 + rndint(M - 1);
                    if (gcd_i(c, M) == 1 && powmod_i(c, K2, M) == 1 % M) {
                        r = c;
                        found = 1;
                    }
                }
                if (!found) continue;
            }

            Group g;
            group_build(&g, M, K2, r);
            Lift L;
            lift_alloc(&L, k, gd, &g);
            int steps = 3000 + 40 * L.N;
            if (steps > 200000) steps = 200000;
            double T0 = (rndint(3) == 0) ? 0.3 : ((rndint(2) == 0) ? 1.0 : 3.0);
            for (int rep = 0; rep < 2 && !time_up(); rep++) {
                lift_random(&L);
                if (lift_anneal(&L, steps, T0) == 0) {
                    emit_lift(&L);
                    break;
                }
            }
            lift_free(&L);
            group_free(&g);
        }
    }

    if (best_n == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", best_eu[i], best_ev[i]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions for small cases, then the C engine.
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to q <= 9."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def build(d, D, seed, time_limit):
    """Return the best valid (n, edges) found within about 85% of time_limit."""
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact constructions (calibration-style cases return immediately).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
    if D == 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search in C: bi-Cayley lifts over semidirect products, seeded with the best so far.
    budget = max(0.3, min(0.85 * time_limit, time_limit - 5.0))
    timeout = max(0.5, min(budget + 4.0, time_limit - 1.5))
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                        stdin_graph=best, timeout=timeout)
        n, e = lib.parse_graph_text(out)
        consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
