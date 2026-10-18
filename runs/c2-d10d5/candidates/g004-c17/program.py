"""d-regular bi-Cayley annealing (C), plus a new C stage that grows the best graph by vertex pairs.

New in this version: the grow stage (GROW_SOURCE). It starts from the best valid graph, keeps
the edge set under degree <= d, and repeatedly (a) adds a pair of isolated vertices once the
current graph is valid, then (b) anneals with add, slot-relocate and 2-switch moves to
minimise the number of pairs at distance > D. The best valid graph seen is returned.
"""
import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine 1: bi-Cayley simulated annealing over Z_m x| Z_k2 (unchanged from parent).
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define PENALTY 1000L
#define KMAX 8

static clock_t g_t0;
static double g_budget = 1.0;
static uint64_t g_rs = 88172645463325252ULL;

/* group Z_m x| Z_k2, element a*k2+b, (a,b)(c,e) = (a + r^b c, b+e) */
static int GM = 1, GK = 1, GG = 1;
static int64_t PW[64];

static long g_best_n = 0;
static long g_best_m = 0;
static int *g_edges = NULL;

static double elapsed(void) {
    return (double)(clock() - g_t0) / (double)CLOCKS_PER_SEC;
}

static uint64_t rnext(void) {
    uint64_t x = g_rs;
    x ^= x >> 12;
    x ^= x << 25;
    x ^= x >> 27;
    g_rs = x;
    return x * 2685821657736338717ULL;
}

static uint64_t rnd(uint64_t n) {
    return n ? rnext() % n : 0;
}

static double rndf(void) {
    return (double)(rnext() >> 11) * (1.0 / 9007199254740992.0);
}

static int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    int64_t t = (a + PW[b] * (int64_t)c) % GM;
    return (int)(t * GK + (b + e) % GK);
}

static int ginv(int x) {
    int a = x / GK, b = x % GK;
    int nb = (GK - b) % GK;
    int64_t t = (-(PW[nb] * (int64_t)a)) % GM;
    if (t < 0) t += GM;
    return (int)(t * GK + nb);
}

static void set_group(int m, int k2, int64_t r) {
    GM = m;
    GK = k2;
    GG = m * k2;
    int64_t p = 1 % m;
    for (int t = 0; t < k2; t++) {
        PW[t] = p;
        p = (p * r) % m;
    }
}

static const int KCH[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};

static int64_t gcd64(int64_t a, int64_t b) {
    while (b) {
        int64_t t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static int64_t powmod(int64_t b, int64_t e, int64_t m) {
    int64_t r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int sample_group(long target, int *mo, int *ko, int64_t *ro) {
    for (int tries = 0; tries < 200; tries++) {
        int k2 = KCH[rnd(20)];
        int64_t m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        int64_t r = 1;
        if (k2 == 1) {
            r = 1;
        } else if (k2 == 2 && rndf() < 0.3) {
            r = m - 1;
            if (gcd64(r, m) != 1 || powmod(r, 2, m) != 1 % m) continue;
        } else {
            int found = 0;
            for (int t = 0; t < 60; t++) {
                int64_t c = (m > 2) ? 2 + (int64_t)rnd((uint64_t)(m - 2)) : 1;
                if (gcd64(c, m) == 1 && powmod(c, k2, m) == 1 % m) {
                    r = c;
                    found = 1;
                    break;
                }
            }
            if (!found) continue;
        }
        *mo = (int)m;
        *ko = k2;
        *ro = r;
        return 1;
    }
    return 0;
}

static int popc(uint32_t x) {
    int c = 0;
    while (x) {
        c += (int)(x & 1u);
        x >>= 1;
    }
    return c;
}

/* A-block i (vertices i*GG..) joins B-block j = lay[l][i] with voltage s = S[l][i]. */
static void set_dart(int **nbr, const int *lay, const int *S, int k, int l, int i) {
    int j = lay[l * k + i];
    int s = S[l * k + i];
    int si = ginv(s);
    int Ab = i * GG, Bb = (k + j) * GG;
    int *nb = nbr[l];
    for (int g = 0; g < GG; g++) {
        nb[Ab + g] = Bb + gmul(g, s);
        nb[Bb + g] = Ab + gmul(g, si);
    }
}

/* out[v] = bitmask of representative blocks within distance D of v. */
static void compute_reach(int **nbr, int d, int k, int N, int D, uint32_t *out, uint32_t *tmp) {
    memset(out, 0, sizeof(uint32_t) * (size_t)N);
    for (int b = 0; b < 2 * k; b++) out[b * GG] = 1u << b;
    for (int t = 0; t < D; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint32_t r = out[v];
            for (int l = 0; l < d; l++) r |= out[nbr[l][v]];
            tmp[v] = r;
            if (r != out[v]) changed = 1;
        }
        memcpy(out, tmp, sizeof(uint32_t) * (size_t)N);
        if (!changed) break;
    }
}

static long unreached(const uint32_t *reach, int k, int N) {
    long s = 0;
    for (int v = 0; v < N; v++) s += popc(reach[v]);
    return 2L * k * N - s;
}

static long dupcount(const int *lay, const int *S, int d, int k) {
    int tot = d * k;
    long dup = 0;
    for (int a = 0; a < tot; a++) {
        int la = a / k, ia = a % k;
        for (int b = 0; b < a; b++) {
            int lb = b / k, ib = b % k;
            if (ia == ib && lay[la * k + ia] == lay[lb * k + ib] && S[la * k + ia] == S[lb * k + ib]) {
                dup++;
                break;
            }
        }
    }
    return dup;
}

static void store_best(int **nbr, int d, int k) {
    long A = (long)k * GG;
    long n = 2 * A;
    if (n <= g_best_n) return;
    long cnt = A * d;
    int *e = malloc(sizeof(int) * 2 * (size_t)cnt);
    if (!e) return;
    long c = 0;
    for (long u = 0; u < A; u++) {
        for (int l = 0; l < d; l++) {
            e[2 * c] = (int)u;
            e[2 * c + 1] = nbr[l][u];
            c++;
        }
    }
    free(g_edges);
    g_edges = e;
    g_best_m = cnt;
    g_best_n = n;
}

static int run_trial(int d, int D, int k, int iters, int patience) {
    int N = 2 * k * GG;
    uint32_t full = (1u << (2 * k)) - 1u;
    int K = d * k;
    int *lay = malloc(sizeof(int) * (size_t)K);
    int *S = malloc(sizeof(int) * (size_t)K);
    int **nbr = malloc(sizeof(int *) * (size_t)d);
    uint32_t *rc = malloc(sizeof(uint32_t) * (size_t)N);
    uint32_t *rn = malloc(sizeof(uint32_t) * (size_t)N);
    uint32_t *tmp = malloc(sizeof(uint32_t) * (size_t)N);
    for (int l = 0; l < d; l++) nbr[l] = malloc(sizeof(int) * (size_t)N);

    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) lay[l * k + i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = (int)rnd((uint64_t)(i + 1));
            int t = lay[l * k + i];
            lay[l * k + i] = lay[l * k + j];
            lay[l * k + j] = t;
        }
    }
    for (int q = 0; q < K; q++) S[q] = (int)rnd((uint64_t)GG);
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) set_dart(nbr, lay, S, k, l, i);

    compute_reach(nbr, d, k, N, D, rc, tmp);
    long cost = unreached(rc, k, N) + PENALTY * dupcount(lay, S, d, k);
    double c0 = cost > 1 ? (double)cost : 1.0;
    long best_cost = cost;
    int last = 0;

    for (int t = 0; t < iters && cost != 0; t++) {
        if (elapsed() > g_budget) break;
        if (t - last > patience) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;

        if (k >= 2 && rndf() < 0.25) {
            int l = (int)rnd((uint64_t)d);
            int i1 = (int)rnd((uint64_t)k);
            int i2 = (int)rnd((uint64_t)(k - 1));
            if (i2 >= i1) i2++;
            int tv = lay[l * k + i1];
            lay[l * k + i1] = lay[l * k + i2];
            lay[l * k + i2] = tv;
            set_dart(nbr, lay, S, k, l, i1);
            set_dart(nbr, lay, S, k, l, i2);
            compute_reach(nbr, d, k, N, D, rn, tmp);
            long c2 = unreached(rn, k, N) + PENALTY * dupcount(lay, S, d, k);
            if (c2 <= cost || rndf() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                uint32_t *p = rc;
                rc = rn;
                rn = p;
                if (cost < best_cost) {
                    best_cost = cost;
                    last = t;
                }
            } else {
                tv = lay[l * k + i1];
                lay[l * k + i1] = lay[l * k + i2];
                lay[l * k + i2] = tv;
                set_dart(nbr, lay, S, k, l, i1);
                set_dart(nbr, lay, S, k, l, i2);
            }
            continue;
        }

        int l = 0, i = 0;
        int picked = 0;
        if (rndf() < 0.4) {
            long nbad = 0;
            for (int v = 0; v < N; v++)
                if (rc[v] != full) nbad++;
            if (nbad > 0) {
                long pick = (long)rnd((uint64_t)nbad);
                int u = -1;
                for (int v = 0; v < N; v++) {
                    if (rc[v] != full) {
                        if (pick == 0) {
                            u = v;
                            break;
                        }
                        pick--;
                    }
                }
                int block = u / GG;
                l = (int)rnd((uint64_t)d);
                if (block < k) {
                    i = block;
                } else {
                    i = -1;
                    for (int q = 0; q < k; q++) {
                        if (lay[l * k + q] == block - k) {
                            i = q;
                            break;
                        }
                    }
                    if (i < 0) i = 0;
                }
                picked = 1;
            }
        }
        if (!picked) {
            l = (int)rnd((uint64_t)d);
            i = (int)rnd((uint64_t)k);
        }

        int old = S[l * k + i];
        int nw = (int)rnd((uint64_t)GG);
        if (nw == old) continue;
        S[l * k + i] = nw;
        set_dart(nbr, lay, S, k, l, i);
        compute_reach(nbr, d, k, N, D, rn, tmp);
        long c2 = unreached(rn, k, N) + PENALTY * dupcount(lay, S, d, k);
        if (c2 <= cost || rndf() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            uint32_t *p = rc;
            rc = rn;
            rn = p;
            if (cost < best_cost) {
                best_cost = cost;
                last = t;
            }
        } else {
            S[l * k + i] = old;
            set_dart(nbr, lay, S, k, l, i);
        }
    }

    int ok = (cost == 0);
    if (ok) store_best(nbr, d, k);

    for (int l = 0; l < d; l++) free(nbr[l]);
    free(nbr);
    free(lay);
    free(S);
    free(rc);
    free(rn);
    free(tmp);
    return ok;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: d D seed budget min_n\n");
        return 1;
    }
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    g_rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (g_rs == 0) g_rs = 1;
    for (int w = 0; w < 10; w++) rnext();
    g_budget = atof(argv[4]);
    g_best_n = atol(argv[5]);
    g_t0 = clock();

    if (d < 1 || D < 1) {
        printf("0 0\n");
        return 0;
    }

    long trials[KMAX + 1], wins[KMAX + 1];
    for (int kk = 0; kk <= KMAX; kk++) {
        trials[kk] = 0;
        wins[kk] = 0;
    }

    while (elapsed() < g_budget) {
        int k;
        if (rndf() < 0.2) {
            k = 1 + (int)rnd(KMAX);
        } else {
            double bv = -1.0;
            k = 1;
            for (int kk = 1; kk <= KMAX; kk++) {
                double v = ((double)wins[kk] + 1.0) / ((double)trials[kk] + 2.0) + 0.02 * rndf();
                if (v > bv) {
                    bv = v;
                    k = kk;
                }
            }
        }
        long base = g_best_n / (2L * k);
        long span = base / 8 + 1;
        if (span < 2) span = 2;
        long target = base + 1 + (long)rnd((uint64_t)span);
        if (target < 2) target = 2;

        int m = 0, k2 = 1;
        int64_t r = 1;
        if (!sample_group(target, &m, &k2, &r)) continue;
        set_group(m, k2, r);
        if (2L * k * GG <= g_best_n) continue;

        trials[k]++;
        if (run_trial(d, D, k, 4000, 1200)) wins[k]++;
    }

    if (g_best_m == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%ld %ld\n", g_best_n, g_best_m);
    for (long c = 0; c < g_best_m; c++) {
        printf("%d %d\n", g_edges[2 * c], g_edges[2 * c + 1]);
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# C engine 2 (new): grow-and-repair on a general bipartite graph with degree <= d.
#   State: graph on N vertices (N grows by pairs), cost = unordered pairs at
#   distance > D (bitset ball computation).
#   Moves: add an edge between two deficient opposite-side vertices;
#          relocate (remove a-b, add a-x for a deficient x, moving the free slot to b);
#          2-switch (degree preserving).
#   Whenever cost == 0, the current graph is stored and a new vertex pair is appended.
#   Output: the largest stored valid graph as "n m" plus edges.
# ----------------------------------------------------------------------------

GROW_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static uint64_t rs = 0x9E3779B97F4A7C15ULL;

static uint64_t rnext(void) {
    uint64_t x = rs;
    x ^= x >> 12;
    x ^= x << 25;
    x ^= x >> 27;
    rs = x;
    return x * 2685821657736338717ULL;
}

static uint64_t rnd(uint64_t n) {
    return n ? rnext() % n : 0;
}

static double rndf(void) {
    return (double)(rnext() >> 11) * (1.0 / 9007199254740992.0);
}

static int d = 1, D = 1, cap = 0, N = 0, WC = 1;
static int *deg = NULL, *side = NULL, *adj = NULL;
static uint64_t *cur = NULL, *nxt = NULL;
static clock_t t0;
static double budget = 1.0;

static int *best_e = NULL;
static long best_m = 0;
static int best_n = 0;

static double elapsed(void) {
    return (double)(clock() - t0) / (double)CLOCKS_PER_SEC;
}

static int has_edge(int u, int v) {
    for (int k = 0; k < deg[u]; k++)
        if (adj[u * d + k] == v) return 1;
    return 0;
}

static void rm_one(int u, int v) {
    for (int k = 0; k < deg[u]; k++) {
        if (adj[u * d + k] == v) {
            adj[u * d + k] = adj[u * d + deg[u] - 1];
            deg[u]--;
            return;
        }
    }
}

static void add_edge(int u, int v) {
    adj[u * d + deg[u]++] = v;
    adj[v * d + deg[v]++] = u;
}

static void del_edge(int u, int v) {
    rm_one(u, v);
    rm_one(v, u);
}

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* number of unordered pairs at distance > D */
static long cost_eval(void) {
    int Wn = (N + 63) / 64;
    for (int v = 0; v < N; v++) {
        uint64_t *p = cur + (size_t)v * WC;
        memset(p, 0, sizeof(uint64_t) * (size_t)Wn);
        p[v >> 6] |= 1ULL << (v & 63);
    }
    for (int t = 0; t < D; t++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt + (size_t)v * WC;
            uint64_t *c = cur + (size_t)v * WC;
            memcpy(o, c, sizeof(uint64_t) * (size_t)Wn);
            for (int k = 0; k < deg[v]; k++) {
                uint64_t *cu = cur + (size_t)adj[v * d + k] * WC;
                for (int w = 0; w < Wn; w++) o[w] |= cu[w];
            }
        }
        uint64_t *tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    long tot = 0;
    for (int v = 0; v < N; v++) {
        uint64_t *c = cur + (size_t)v * WC;
        for (int w = 0; w < Wn; w++) tot += popc64(c[w]);
    }
    return (((long)N * N) - tot) / 2;
}

static void store_best(void) {
    long m = 0;
    for (int v = 0; v < N; v++) m += deg[v];
    m /= 2;
    int *e = malloc(sizeof(int) * 2 * (size_t)(m > 0 ? m : 1));
    if (!e) return;
    long c = 0;
    for (int u = 0; u < N; u++) {
        for (int k = 0; k < deg[u]; k++) {
            int v = adj[u * d + k];
            if (u < v) {
                e[2 * c] = u;
                e[2 * c + 1] = v;
                c++;
            }
        }
    }
    free(best_e);
    best_e = e;
    best_m = c;
    best_n = N;
}

static int accept(long delta, double T) {
    if (delta <= 0) return 1;
    return rndf() < exp(-(double)delta / T);
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: d D seed budget maxpairs\n");
        return 1;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 10; w++) rnext();
    budget = atof(argv[4]);
    int maxpairs = atoi(argv[5]);
    t0 = clock();

    if (d < 1 || D < 1 || d > 32) {
        printf("0 0\n");
        return 0;
    }
    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2 || n < 1 || m < 0) {
        printf("0 0\n");
        return 0;
    }
    if (maxpairs < 0) maxpairs = 0;
    cap = n + 2 * maxpairs;
    WC = (cap + 63) / 64;
    deg = calloc((size_t)cap, sizeof(int));
    side = calloc((size_t)cap, sizeof(int));
    adj = calloc((size_t)cap * d, sizeof(int));
    cur = calloc((size_t)cap * WC, sizeof(uint64_t));
    nxt = calloc((size_t)cap * WC, sizeof(uint64_t));
    int *queue = calloc((size_t)cap, sizeof(int));
    if (!deg || !side || !adj || !cur || !nxt || !queue) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) {
            printf("0 0\n");
            return 0;
        }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v || has_edge(u, v) || deg[u] >= d || deg[v] >= d) {
            printf("0 0\n");
            return 0;
        }
        add_edge(u, v);
    }

    /* bipartition by BFS; reject odd cycles */
    for (int v = 0; v < N; v++) side[v] = -1;
    for (int s = 0; s < N; s++) {
        if (side[s] != -1) continue;
        side[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int u = queue[qh++];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[u * d + k];
                if (side[v] == -1) {
                    side[v] = 1 - side[u];
                    queue[qt++] = v;
                } else if (side[v] == side[u]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }

    long cost = cost_eval();
    while (elapsed() < budget) {
        if (cost == 0) {
            store_best();
            if (N + 2 > cap) break;
            side[N] = 0;
            side[N + 1] = 1;
            deg[N] = 0;
            deg[N + 1] = 0;
            N += 2;
            cost = cost_eval();
            continue;
        }

        double frac = 1.0 - elapsed() / budget;
        if (frac < 0) frac = 0;
        double T = 0.2 + 0.01 * (double)cost * frac;
        double r = rndf();
        long old = cost, c2;

        if (r < 0.3) {
            /* add an edge between two deficient opposite-side vertices */
            int u = (int)rnd((uint64_t)N), v = (int)rnd((uint64_t)N);
            if (side[u] == side[v] || deg[u] >= d || deg[v] >= d || has_edge(u, v)) continue;
            add_edge(u, v);
            c2 = cost_eval();
            if (accept(c2 - old, T)) cost = c2;
            else del_edge(u, v);
        } else if (r < 0.7) {
            /* relocate: free slot of x taken from neighbour b of a, edge a-b becomes a-x */
            int x = (int)rnd((uint64_t)N);
            if (deg[x] >= d) continue;
            int a = (int)rnd((uint64_t)N);
            if (side[a] == side[x] || deg[a] == 0 || has_edge(a, x)) continue;
            int b = adj[a * d + (int)rnd((uint64_t)deg[a])];
            del_edge(a, b);
            add_edge(a, x);
            c2 = cost_eval();
            if (accept(c2 - old, T)) {
                cost = c2;
            } else {
                del_edge(a, x);
                add_edge(a, b);
            }
        } else {
            /* 2-switch, degree preserving */
            int u1 = (int)rnd((uint64_t)N);
            if (deg[u1] == 0) continue;
            int v1 = adj[u1 * d + (int)rnd((uint64_t)deg[u1])];
            int u2 = (int)rnd((uint64_t)N);
            if (u2 == u1 || side[u2] != side[u1] || deg[u2] == 0) continue;
            int v2 = adj[u2 * d + (int)rnd((uint64_t)deg[u2])];
            if (v1 == v2 || has_edge(u1, v2) || has_edge(u2, v1)) continue;
            del_edge(u1, v1);
            del_edge(u2, v2);
            add_edge(u1, v2);
            add_edge(u2, v1);
            c2 = cost_eval();
            if (accept(c2 - old, T)) {
                cost = c2;
            } else {
                del_edge(u1, v2);
                del_edge(u2, v1);
                add_edge(u1, v1);
                add_edge(u2, v2);
            }
        }
    }
    if (cost == 0) store_best();

    if (best_n == 0 || best_e == NULL) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %ld\n", best_n, best_m);
    for (long c = 0; c < best_m; c++) {
        printf("%d %d\n", best_e[2 * c], best_e[2 * c + 1]);
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Safe baseline families.
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Runners.
# ----------------------------------------------------------------------------

def _c_search(d, D, seed, budget, min_n, timeout):
    """Run the bi-Cayley engine; returns (n, edges), or (0, []) if nothing beat min_n."""
    text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", min_n], timeout=timeout)
    return lib.parse_graph_text(text)


def _grow(n, edges, d, D, seed, budget, maxpairs, timeout):
    """Run the grow-and-repair engine from a valid start graph; returns (n, edges)."""
    text = lib.run_c(GROW_SOURCE, [d, D, seed, f"{budget:.2f}", maxpairs],
                     stdin_graph=(n, edges), timeout=timeout)
    return lib.parse_graph_text(text)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.88 * time_limit, time_limit - 6.0))
    deadline = start + budget

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

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Phase 1: bi-Cayley annealing (60% of the remaining budget).
    c_budget = (deadline - time.monotonic()) * 0.6
    if c_budget > 0.5:
        timeout = max(1.0, min(c_budget + 3.0, time_limit - (time.monotonic() - start) - 1.5))
        try:
            n, e = _c_search(d, D, seed, c_budget, best_n, timeout)
            consider(n, e)
        except Exception:
            pass

    # Phase 2: grow-and-repair from the best valid graph (rest of the budget).
    g_budget = deadline - time.monotonic() - 1.0
    if g_budget > 1.0 and best_n >= 4:
        maxpairs = max(2, min(300, best_n // 60))
        timeout = max(1.0, min(g_budget + 3.0, time_limit - (time.monotonic() - start) - 1.5))
        try:
            n, e = _grow(best[0], best[1], d, D, seed, g_budget, maxpairs, timeout)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
