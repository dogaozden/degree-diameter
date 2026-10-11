"""Two-stage search for large bipartite graphs with max degree d and diameter <= D.

Stage A (LIFT_SOURCE): the parent's bi-Cayley lift annealer over metacyclic groups. It
  supplies a strong valid starting graph (336 vertices for d=5, D=5).

Stage B (GROW_SOURCE, new): a general-graph engine that works on the start graph
  directly. Each attempt adds one vertex on each side, rewires the graph so it stays
  d-regular and bipartite, and then anneals over degree-preserving 2-switches to remove
  all pairs at distance > D. Failed attempts restore the best valid graph and retry.
  Every success is snapshotted, so the output is always the largest valid graph found.

Safety: every returned graph is checked with lib.is_valid. The fallback is the best of
K_{d,d} and PG(2,q) incidence graphs, and it is returned whenever the C stages fail.
"""
import time

import lib


LIFT_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK 8
#define MAXK2 64

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double cpu_now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

typedef struct {
    int G, m, k2;
    long long r;
    long long pw[MAXK2];
} Group;

static long long lmod(long long a, long long m) {
    a %= m;
    return a < 0 ? a + m : a;
}

static long long gcdll(long long a, long long b) {
    if (a < 0) a = -a;
    if (b < 0) b = -b;
    while (b) {
        long long t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b = lmod(b, m);
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static void make_group(Group *g, int G, int k2, int m, long long r) {
    g->G = G;
    g->m = m;
    g->k2 = k2;
    g->r = r;
    g->pw[0] = 1 % m;
    for (int b = 1; b < k2; b++) g->pw[b] = (g->pw[b - 1] * r) % m;
}

static int gmul(const Group *g, int x, int y) {
    int a = x / g->k2, b = x % g->k2, c = y / g->k2, e = y % g->k2;
    long long na = lmod((long long)a + g->pw[b] * (long long)c, g->m);
    int nb = (b + e) % g->k2;
    return (int)(na * g->k2 + nb);
}

static int ginv(const Group *g, int x) {
    int a = x / g->k2, b = x % g->k2;
    int nb = (g->k2 - b) % g->k2;
    long long na = lmod(-g->pw[nb] * (long long)a, g->m);
    return (int)(na * g->k2 + nb);
}

static void random_group(Group *g, int G) {
    int cand[256];
    int nc = 0;
    for (int k2 = 1; k2 <= MAXK2 && k2 <= G; k2++)
        if (G % k2 == 0 && G / k2 >= 2) cand[nc++] = k2;
    int k2 = cand[rndint(nc)];
    int m = G / k2;
    long long r = 1 % m;
    if (k2 > 1) {
        for (int t = 0; t < 300; t++) {
            long long c = 1 + rndint(m - 1);
            if (gcdll(c, m) == 1 && powmod(c, k2, m) == 1 % m) {
                r = c;
                break;
            }
        }
    }
    make_group(g, G, k2, m, r);
}

typedef struct {
    int k, d, G, N, stamp;
    Group grp;
    int *dj, *ds, *dsi;
    int *adj, *vis, *queue;
} Lift;

static void lift_alloc(Lift *L, int k, int d, int G) {
    L->k = k;
    L->d = d;
    L->G = G;
    L->N = 2 * k * G;
    L->stamp = 0;
    L->dj = malloc(sizeof(int) * (size_t)(k * d));
    L->ds = malloc(sizeof(int) * (size_t)(k * d));
    L->dsi = malloc(sizeof(int) * (size_t)(k * d));
    L->adj = malloc(sizeof(int) * (size_t)L->N * (size_t)d);
    L->vis = calloc((size_t)L->N, sizeof(int));
    L->queue = malloc(sizeof(int) * (size_t)L->N);
}

static void lift_free(Lift *L) {
    free(L->dj);
    free(L->ds);
    free(L->dsi);
    free(L->adj);
    free(L->vis);
    free(L->queue);
}

static void random_init(Lift *L) {
    int k = L->k, d = L->d;
    for (int l = 0; l < d; l++) {
        int perm[MAXK];
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i];
            perm[i] = perm[j];
            perm[j] = t;
        }
        for (int i = 0; i < k; i++) {
            int idx = l * k + i;
            L->dj[idx] = perm[i];
            L->ds[idx] = rndint(L->G);
            L->dsi[idx] = ginv(&L->grp, L->ds[idx]);
        }
    }
}

static void build_adj(Lift *L) {
    int k = L->k, d = L->d, G = L->G;
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) {
            int idx = l * k + i;
            int j = L->dj[idx], s = L->ds[idx], si = L->dsi[idx];
            for (int x = 0; x < G; x++) {
                int a = i * G + x;
                L->adj[(size_t)a * d + l] = (k + j) * G + gmul(&L->grp, x, s);
                int b = (k + j) * G + x;
                L->adj[(size_t)b * d + l] = i * G + gmul(&L->grp, x, si);
            }
        }
    }
}

static int count_dups(const Lift *L) {
    int c = 0;
    for (int i = 0; i < L->k; i++)
        for (int l = 0; l < L->d; l++)
            for (int l2 = l + 1; l2 < L->d; l2++) {
                int a = l * L->k + i, b = l2 * L->k + i;
                if (L->dj[a] == L->dj[b] && L->ds[a] == L->ds[b]) c++;
            }
    return c;
}

static long long eval_cost(Lift *L, int D) {
    int k = L->k, d = L->d, G = L->G, N = L->N;
    long long cost = (long long)count_dups(L) * (long long)N;
    build_adj(L);
    for (int rep = 0; rep < 2 * k; rep++) {
        int src = rep * G;
        if (++L->stamp >= 0x7ffffff0) {
            memset(L->vis, 0, sizeof(int) * (size_t)N);
            L->stamp = 1;
        }
        int head = 0, tail = 0;
        L->queue[tail++] = src;
        L->vis[src] = L->stamp;
        for (int depth = 0; depth < D && head < tail; depth++) {
            int end = tail;
            while (head < end) {
                int u = L->queue[head++];
                const int *au = L->adj + (size_t)u * d;
                for (int t = 0; t < d; t++) {
                    int v = au[t];
                    if (L->vis[v] != L->stamp) {
                        L->vis[v] = L->stamp;
                        L->queue[tail++] = v;
                    }
                }
            }
        }
        cost += N - tail;
    }
    return cost;
}

static int anneal(Lift *L, int D, long long iters, double T0, double T1, double tend) {
    int k = L->k, d = L->d, G = L->G;
    long long cost = eval_cost(L, D);
    if (cost == 0) return 1;
    for (long long it = 0; it < iters; it++) {
        if ((it & 127) == 0 && cpu_now() > tend) return 0;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        long long c2;
        if (k >= 2 && rnd01() < 0.4) {
            int l = rndint(d);
            int i1 = rndint(k);
            int i2 = rndint(k - 1);
            if (i2 >= i1) i2++;
            int a = l * k + i1, b = l * k + i2;
            int t = L->dj[a];
            L->dj[a] = L->dj[b];
            L->dj[b] = t;
            c2 = eval_cost(L, D);
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                t = L->dj[a];
                L->dj[a] = L->dj[b];
                L->dj[b] = t;
            }
        } else {
            int idx = rndint(d * k);
            int os = L->ds[idx], osi = L->dsi[idx];
            int ns = rndint(G);
            if (ns == os) continue;
            L->ds[idx] = ns;
            L->dsi[idx] = ginv(&L->grp, ns);
            c2 = eval_cost(L, D);
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                L->ds[idx] = os;
                L->dsi[idx] = osi;
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    int c;
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed budget\n");
        return 1;
    }
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 20; w++) rnd64();
    while ((c = getchar()) != EOF) {
    }

    if (d < 2 || D < 2) {
        printf("0 0\n");
        return 0;
    }

    double tend = cpu_now() + budget;
    int best_n = 0, best_m = 0;
    int *best_e = NULL;

    while (cpu_now() < tend) {
        int k = 1 + rndint(4);
        int Gmin = best_n / (2 * k) + 1;
        if (Gmin < 2) Gmin = 2;
        int spread = Gmin / 12 + 2;
        int G = Gmin + rndint(spread);

        Lift L;
        lift_alloc(&L, k, d, G);
        random_group(&L.grp, G);
        random_init(&L);
        int ok = anneal(&L, D, 100000, 3.0, 0.15, tend);
        if (ok) {
            build_adj(&L);
            int cnt = k * G * d;
            int *e = malloc(sizeof(int) * 2 * (size_t)cnt);
            int m = 0;
            for (int i = 0; i < k; i++)
                for (int x = 0; x < G; x++)
                    for (int l = 0; l < d; l++) {
                        int a = i * G + x;
                        e[2 * m] = a;
                        e[2 * m + 1] = L.adj[(size_t)a * d + l];
                        m++;
                    }
            if (L.N > best_n) {
                free(best_e);
                best_e = e;
                best_n = L.N;
                best_m = m;
            } else {
                free(e);
            }
        }
        lift_free(&L);
    }

    if (best_n == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", best_n, best_m);
    for (int t = 0; t < best_m; t++) printf("%d %d\n", best_e[2 * t], best_e[2 * t + 1]);
    free(best_e);
    return 0;
}
"""


GROW_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXCAP 3200
#define EXTRA 400
#define STEP_IT 50000

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double cpu_now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

/* State: d-regular bipartite graph. Side 0 endpoint is ea[e], side 1 endpoint is eb[e]. */
static int d, D, N, M, CAP;
static int *ea, *eb, *nb, *dg, *vis, *qu, *bEa, *bEb;
static unsigned char *adjm;
static int stamp_ = 0;
static int best_N = 0, best_M = 0;
static long long moore;
static double tend;

static void alloc_all(void) {
    ea = malloc(sizeof(int) * (size_t)(CAP * d + d + 4));
    eb = malloc(sizeof(int) * (size_t)(CAP * d + d + 4));
    bEa = malloc(sizeof(int) * (size_t)(CAP * d + d + 4));
    bEb = malloc(sizeof(int) * (size_t)(CAP * d + d + 4));
    nb = malloc(sizeof(int) * (size_t)CAP * d);
    dg = calloc((size_t)CAP, sizeof(int));
    vis = calloc((size_t)CAP, sizeof(int));
    qu = malloc(sizeof(int) * (size_t)CAP);
    adjm = calloc((size_t)CAP * CAP, 1);
}

static void setadj(int u, int v, int val) {
    adjm[(size_t)u * CAP + v] = (unsigned char)val;
    adjm[(size_t)v * CAP + u] = (unsigned char)val;
}

/* In vertex v's neighbour list replace old by nw. */
static void rep(int v, int old, int nw) {
    int *a = nb + (size_t)v * d;
    for (int t = 0; t < d; t++)
        if (a[t] == old) { a[t] = nw; return; }
}

/* Rebuild nb, dg and adjm from ea/eb (N, M current). */
static void rebuild(void) {
    memset(adjm, 0, (size_t)CAP * CAP);
    for (int v = 0; v < N; v++) dg[v] = 0;
    for (int e = 0; e < M; e++) {
        int u = ea[e], v = eb[e];
        nb[(size_t)u * d + dg[u]++] = v;
        nb[(size_t)v * d + dg[v]++] = u;
        setadj(u, v, 1);
    }
}

static long long eval_cost(void) {
    long long cost = 0;
    for (int s = 0; s < N; s++) {
        if (++stamp_ >= 0x7ffffff0) {
            memset(vis, 0, sizeof(int) * (size_t)CAP);
            stamp_ = 1;
        }
        int head = 0, tail = 0;
        qu[tail++] = s;
        vis[s] = stamp_;
        for (int dep = 0; dep < D && head < tail; dep++) {
            int end = tail;
            while (head < end) {
                int u = qu[head++];
                const int *au = nb + (size_t)u * d;
                for (int t = 0; t < d; t++) {
                    int v = au[t];
                    if (vis[v] != stamp_) {
                        vis[v] = stamp_;
                        qu[tail++] = v;
                    }
                }
            }
        }
        cost += N - tail;
    }
    return cost;
}

/* Edges (x1,y1),(x2,y2) become (x1,y2),(x2,y1). Applying twice restores the original. */
static void do_switch(int e1, int e2) {
    int x1 = ea[e1], y1 = eb[e1], x2 = ea[e2], y2 = eb[e2];
    rep(x1, y1, y2);
    rep(y2, x2, x1);
    rep(x2, y2, y1);
    rep(y1, x1, x2);
    setadj(x1, y1, 0);
    setadj(x2, y2, 0);
    setadj(x1, y2, 1);
    setadj(x2, y1, 1);
    eb[e1] = y2;
    eb[e2] = y1;
}

static int anneal(long long maxit) {
    long long cost = eval_cost();
    if (cost == 0) return 1;
    double T0 = 2.0, T1 = 0.15;
    for (long long it = 0; it < maxit; it++) {
        if ((it & 31) == 0 && cpu_now() > tend) return 0;
        double T = T0 * pow(T1 / T0, (double)it / (double)maxit);
        int e1 = rndint(M), e2 = rndint(M);
        if (e1 == e2) continue;
        int x1 = ea[e1], y1 = eb[e1], x2 = ea[e2], y2 = eb[e2];
        if (x1 == x2 || y1 == y2) continue;
        if (adjm[(size_t)x1 * CAP + y2] || adjm[(size_t)x2 * CAP + y1]) continue;
        do_switch(e1, e2);
        long long c2 = eval_cost();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
            if (cost == 0) return 1;
        } else {
            do_switch(e1, e2);
        }
    }
    return 0;
}

/* Add one new side-0 vertex p and one new side-1 vertex q, each with degree d.
   Each step takes an old edge (x,y) and rewires it to (p,y) and (x,q). */
static int grow_two(void) {
    if (N + 2 > CAP || (long long)N + 2 > moore) return 0;
    int oldN = N, p = N, q = N + 1;
    N += 2;
    dg[p] = 0;
    dg[q] = 0;
    for (int k = 0; k < d; k++) {
        int e = -1, x = -1, y = -1, ok = 0;
        for (int tries = 0; tries < 2000000 && !ok; tries++) {
            e = rndint(M);
            x = ea[e];
            y = eb[e];
            if (x >= oldN || y >= oldN) continue;
            if (adjm[(size_t)x * CAP + q] || adjm[(size_t)p * CAP + y]) continue;
            ok = 1;
        }
        if (!ok) return 0;
        rep(x, y, q);
        rep(y, x, p);
        setadj(x, y, 0);
        setadj(p, y, 1);
        setadj(x, q, 1);
        nb[(size_t)p * d + dg[p]++] = y;
        nb[(size_t)q * d + dg[q]++] = x;
        ea[e] = p;
        eb[e] = y;
        ea[M] = x;
        eb[M] = q;
        M++;
    }
    return 1;
}

static void snapshot(void) {
    best_N = N;
    best_M = M;
    memcpy(bEa, ea, sizeof(int) * (size_t)M);
    memcpy(bEb, eb, sizeof(int) * (size_t)M);
}

static void restore(void) {
    N = best_N;
    M = best_M;
    memcpy(ea, bEa, sizeof(int) * (size_t)M);
    memcpy(eb, bEb, sizeof(int) * (size_t)M);
    rebuild();
}

static int load_graph(void) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n < 2 || n > MAXCAP - EXTRA || m < 0) return 0;
    if ((long long)m * 2 != (long long)n * d) return 0;
    CAP = n + EXTRA;
    int *eu = malloc(sizeof(int) * (size_t)(m + 1));
    int *ev = malloc(sizeof(int) * (size_t)(m + 1));
    int *dc = calloc((size_t)n, sizeof(int));
    int ok = 1;
    for (int i = 0; i < m; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) { ok = 0; break; }
        if (eu[i] < 0 || eu[i] >= n || ev[i] < 0 || ev[i] >= n || eu[i] == ev[i]) { ok = 0; break; }
        dc[eu[i]]++;
        dc[ev[i]]++;
    }
    for (int v = 0; ok && v < n; v++)
        if (dc[v] != d) ok = 0;
    if (!ok) {
        free(eu); free(ev); free(dc);
        return 0;
    }
    alloc_all();
    N = n;
    M = m;
    /* Build neighbour lists and reject duplicate edges. */
    for (int v = 0; v < n; v++) dg[v] = 0;
    for (int i = 0; i < m && ok; i++) {
        int u = eu[i], v = ev[i];
        if (adjm[(size_t)u * CAP + v]) { ok = 0; break; }
        setadj(u, v, 1);
        nb[(size_t)u * d + dg[u]++] = v;
        nb[(size_t)v * d + dg[v]++] = u;
    }
    /* Bipartition by BFS; fails if an odd cycle exists. */
    int *side = malloc(sizeof(int) * (size_t)n);
    for (int v = 0; v < n; v++) side[v] = -1;
    for (int s = 0; ok && s < n; s++) {
        if (side[s] != -1) continue;
        side[s] = 0;
        int head = 0, tail = 0;
        qu[tail++] = s;
        while (head < tail && ok) {
            int u = qu[head++];
            for (int t = 0; t < d; t++) {
                int w = nb[(size_t)u * d + t];
                if (side[w] == -1) {
                    side[w] = 1 - side[u];
                    qu[tail++] = w;
                } else if (side[w] == side[u]) {
                    ok = 0;
                    break;
                }
            }
        }
    }
    if (ok) {
        for (int i = 0; i < m; i++) {
            int u = eu[i], v = ev[i];
            if (side[u] == 0) { ea[i] = u; eb[i] = v; }
            else { ea[i] = v; eb[i] = u; }
        }
    }
    free(side);
    free(eu);
    free(ev);
    free(dc);
    return ok;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 20; w++) rnd64();
    tend = cpu_now() + budget;

    if (d < 2 || D < 2 || !load_graph()) {
        printf("0 0\n");
        return 0;
    }

    /* Moore bound for bipartite graphs: 2 * sum_{i<D} (d-1)^i (for d >= 3). */
    if (d == 2) {
        moore = 2LL * D;
    } else {
        moore = 0;
        long long term = 1;
        for (int i = 0; i < D && moore < 1000000000LL; i++) {
            moore += term;
            term *= (d - 1);
        }
        moore *= 2;
    }

    int valid = (eval_cost() == 0);
    if (!valid) valid = anneal(200000);
    if (!valid) {
        printf("0 0\n");
        return 0;
    }
    snapshot();

    while (cpu_now() < tend) {
        restore();
        if (!grow_two()) {
            /* Only stops at the Moore limit or capacity. Otherwise retry with new random choices. */
            if ((long long)best_N + 2 > moore || best_N + 2 > CAP) break;
            continue;
        }
        if (anneal(STEP_IT)) snapshot();
    }

    printf("%d %d\n", best_N, best_M);
    for (int e = 0; e < best_M; e++) printf("%d %d\n", bEa[e], bEb[e]);
    return 0;
}
"""


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
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

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Calibration cases already at the Moore bound: nothing to search.
    if d < 2 or best_n >= lib.moore_bound(d, D):
        return best

    deadline = t0 + 0.8 * time_limit - 3.0
    if deadline - time.monotonic() < 4.0:
        return best

    # Stage A: lift search gives a strong start graph.
    budget_a = 0.4 * (deadline - time.monotonic())
    if budget_a > 1.0:
        try:
            text = lib.run_c(LIFT_SOURCE, [d, D, seed, f"{budget_a:.2f}"],
                             stdin_graph=None, timeout=budget_a + 5.0)
            consider(*lib.parse_graph_text(text))
        except (RuntimeError, ValueError, OSError):
            pass

    # Stage B: grow the best valid graph by annealing over degree-preserving 2-switches.
    budget_b = deadline - time.monotonic() - 0.5
    if budget_b > 1.0:
        try:
            text = lib.run_c(GROW_SOURCE, [d, D, seed + 1, f"{budget_b:.2f}"],
                             stdin_graph=best, timeout=budget_b + 8.0)
            consider(*lib.parse_graph_text(text))
        except (RuntimeError, ValueError, OSError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
