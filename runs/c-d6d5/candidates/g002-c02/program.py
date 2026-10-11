"""Two-stage search for bipartite graphs with max degree d and diameter D.

Stage 0: projective-plane and generalized-quadrangle baselines (always valid, used as fallback).
Stage 1: C group-voltage lift annealing (as before) to get a large regular start graph.
Stage 2 (new): full-graph local search. A C engine takes the best graph so far and
  (a) anneals with degree-preserving bipartite 2-switches, minimising the number of
      vertex pairs at distance > D (computed with bitset BFS), and
  (b) whenever the graph is valid, grows it by two vertices (one per side) by
      re-routing d existing edges through them, then anneals again.
Every output is re-checked with lib.is_valid, and the baseline is kept as the fallback.
"""
import itertools
import time

import lib


C_LIFT = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define BIGC 1000000000LL

static void *xmalloc(size_t n) {
    void *p = malloc(n ? n : 1);
    if (!p) { fprintf(stderr, "out of memory\n"); exit(1); }
    return p;
}
static void *xcalloc(size_t n, size_t sz) {
    void *p = calloc(n ? n : 1, sz ? sz : 1);
    if (!p) { fprintf(stderr, "out of memory\n"); exit(1); }
    return p;
}

static double wall_now(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

typedef struct { uint64_t s; } Rng;

static uint64_t rng_next(Rng *r) {
    uint64_t z = (r->s += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}
static int rng_int(Rng *r, int n) { return (int)(rng_next(r) % (uint64_t)n); }
static double rng_unit(Rng *r) { return (double)(rng_next(r) >> 11) * (1.0 / 9007199254740992.0); }

static int gcd_int(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}
static int powmod(int b, int e, int m) {
    long long r = 1 % m, x = b % m;
    while (e > 0) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

/* Group Z_M x| Z_K2, element a*K2+b, (a,b)(c,e) = (a + r^b c, b + e). */
typedef struct {
    int G, M, K2, r;
    int pw[16];
} Group;

static int gmul(const Group *g, int x, int y) {
    int a = x / g->K2, b = x % g->K2;
    int c = y / g->K2, e = y % g->K2;
    long long t = ((long long)a + (long long)g->pw[b] * c) % g->M;
    return (int)(t * g->K2 + (b + e) % g->K2);
}

static int sample_group(Rng *rng, int G, Group *out) {
    static const int K2s[13] = {1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12};
    for (int tries = 0; tries < 80; tries++) {
        int k2 = K2s[rng_int(rng, 13)];
        if (G % k2) continue;
        int M = G / k2;
        if (M < 2) continue;
        int r = 1;
        if (k2 > 1) {
            int found = 0;
            for (int t = 0; t < 200 && !found; t++) {
                int cand = 1 + rng_int(rng, M - 1);
                if (gcd_int(cand, M) == 1 && powmod(cand, k2, M) == 1 % M) {
                    r = cand;
                    found = 1;
                }
            }
            if (!found) continue;
        }
        out->G = G;
        out->M = M;
        out->K2 = k2;
        out->r = r;
        out->pw[0] = 1 % M;
        for (int b = 1; b < k2; b++)
            out->pw[b] = (int)((long long)out->pw[b - 1] * r % M);
        return 1;
    }
    return 0;
}

/* Voltage lift state. Dart t has base A vertex i = t % k, base B vertex dJ[t], voltage dS[t].
   Layer l = t / k holds a permutation over i -> dJ, so every A and B vertex has degree d. */
typedef struct {
    int d, D, k, G, N, nd;
    Group gr;
    int *dJ, *dS, *bS, *bJ, *bestS, *bestJ;
    int *adj, *cnt, *seen, *q;
    int stamp;
} State;

static void state_init(State *st, int d, int D, int k, int G, const Group *gr) {
    st->d = d;
    st->D = D;
    st->k = k;
    st->G = G;
    st->N = 2 * k * G;
    st->nd = d * k;
    st->gr = *gr;
    st->stamp = 0;
    st->dJ = xmalloc(sizeof(int) * (size_t)st->nd);
    st->dS = xmalloc(sizeof(int) * (size_t)st->nd);
    st->bS = xmalloc(sizeof(int) * (size_t)st->nd);
    st->bJ = xmalloc(sizeof(int) * (size_t)st->nd);
    st->bestS = xmalloc(sizeof(int) * (size_t)st->nd);
    st->bestJ = xmalloc(sizeof(int) * (size_t)st->nd);
    st->adj = xmalloc(sizeof(int) * (size_t)st->N * (size_t)d);
    st->cnt = xcalloc((size_t)st->N, sizeof(int));
    st->seen = xcalloc((size_t)st->N, sizeof(int));
    st->q = xmalloc(sizeof(int) * (size_t)st->N);
}

static void state_free(State *st) {
    free(st->dJ); free(st->dS); free(st->bS); free(st->bJ);
    free(st->bestS); free(st->bestJ);
    free(st->adj); free(st->cnt); free(st->seen); free(st->q);
}

/* Number of (representative, vertex) pairs at distance > D; 0 means valid. */
static long long eval_cost(State *st) {
    int k = st->k, G = st->G, d = st->d, D = st->D, N = st->N, nd = st->nd;
    int *adj = st->adj, *cnt = st->cnt;

    for (int t1 = 0; t1 < nd; t1++)
        for (int t2 = t1 + 1; t2 < nd; t2++)
            if (t1 % k == t2 % k && st->dJ[t1] == st->dJ[t2] && st->dS[t1] == st->dS[t2])
                return BIGC;

    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int t = 0; t < nd; t++) {
        int i = t % k, j = st->dJ[t], s = st->dS[t];
        for (int g = 0; g < G; g++) {
            int a = i * G + g;
            int b = (k + j) * G + gmul(&st->gr, g, s);
            if (cnt[a] < d) adj[a * d + cnt[a]++] = b;
            if (cnt[b] < d) adj[b * d + cnt[b]++] = a;
        }
    }

    long long total = 0;
    for (int rep = 0; rep < 2 * k; rep++) {
        int src = rep * G;
        int stamp = ++st->stamp;
        int *seen = st->seen, *q = st->q;
        int head = 0, tail = 0;
        q[tail++] = src;
        seen[src] = stamp;
        for (int lev = 0; lev < D && head < tail; lev++) {
            int end = tail;
            while (head < end) {
                int u = q[head++];
                int *nb = adj + (size_t)u * (size_t)d;
                for (int e = 0; e < cnt[u]; e++) {
                    int v = nb[e];
                    if (seen[v] != stamp) {
                        seen[v] = stamp;
                        q[tail++] = v;
                    }
                }
            }
        }
        total += N - tail;
    }
    return total;
}

static long long anneal(State *st, Rng *rng, long iters, double deadline) {
    int k = st->k, d = st->d, nd = st->nd, G = st->G;

    for (int l = 0; l < d; l++) {
        int *p = st->dJ + l * k;
        for (int i = 0; i < k; i++) p[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rng_int(rng, i + 1);
            int tmp = p[i]; p[i] = p[j]; p[j] = tmp;
        }
    }
    for (int t = 0; t < nd; t++) st->dS[t] = rng_int(rng, G);

    long long cost = eval_cost(st);
    long long best = cost;
    memcpy(st->bestS, st->dS, sizeof(int) * (size_t)nd);
    memcpy(st->bestJ, st->dJ, sizeof(int) * (size_t)nd);

    for (long it = 0; it < iters && best > 0; it++) {
        if ((it & 255) == 0 && wall_now() > deadline) break;
        double T = 3.0 * (1.0 - (double)it / (double)iters) + 0.05;
        memcpy(st->bS, st->dS, sizeof(int) * (size_t)nd);
        memcpy(st->bJ, st->dJ, sizeof(int) * (size_t)nd);

        if (k > 1 && rng_unit(rng) < 0.3) {
            int l = rng_int(rng, d), i1 = rng_int(rng, k), i2 = rng_int(rng, k);
            if (i1 == i2) continue;
            int *p = st->dJ + l * k;
            int tmp = p[i1]; p[i1] = p[i2]; p[i2] = tmp;
        } else {
            st->dS[rng_int(rng, nd)] = rng_int(rng, G);
        }

        long long c2 = eval_cost(st);
        if (c2 <= cost || rng_unit(rng) < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
            if (cost < best) {
                best = cost;
                memcpy(st->bestS, st->dS, sizeof(int) * (size_t)nd);
                memcpy(st->bestJ, st->dJ, sizeof(int) * (size_t)nd);
            }
        } else {
            memcpy(st->dS, st->bS, sizeof(int) * (size_t)nd);
            memcpy(st->dJ, st->bJ, sizeof(int) * (size_t)nd);
        }
    }
    return best;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: prog d D seed time_limit n0\n");
        return 1;
    }
    int d = atoi(argv[1]), D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tlim = atof(argv[4]);
    int n0 = atoi(argv[5]);

    if (d < 2 || D < 2 || d > 64) {
        printf("0 0\n");
        return 0;
    }

    double deadline = wall_now() + tlim;
    Rng rng;
    rng.s = seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;

    int maxnd = 3 * d;
    int *outJ = xmalloc(sizeof(int) * (size_t)maxnd);
    int *outS = xmalloc(sizeof(int) * (size_t)maxnd);
    int have = 0, best_n = n0, bk = 0, bG = 0;
    Group bgr;
    memset(&bgr, 0, sizeof(bgr));

    while (wall_now() < deadline) {
        int r = rng_int(&rng, 5);
        int k = (r < 2) ? 1 : ((r < 4) ? 2 : 3);
        int base = best_n / (2 * k);
        int spread = base / 6 + 2;
        int G = base + 1 + rng_int(&rng, spread);
        if (G < 2) G = 2;

        Group gr;
        if (!sample_group(&rng, G, &gr)) continue;

        State st;
        state_init(&st, d, D, k, G, &gr);
        long long res = anneal(&st, &rng, 40000, deadline);
        if (res == 0) {
            int n = 2 * k * G;
            if (n > best_n) {
                best_n = n;
                have = 1;
                bk = k;
                bG = G;
                bgr = gr;
                memcpy(outJ, st.bestJ, sizeof(int) * (size_t)st.nd);
                memcpy(outS, st.bestS, sizeof(int) * (size_t)st.nd);
            }
        }
        state_free(&st);
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    int k = bk, G = bG, nd = d * k, N = 2 * k * G;
    printf("%d %d\n", N, nd * G);
    for (int t = 0; t < nd; t++) {
        int i = t % k, j = outJ[t], s = outS[t];
        for (int g = 0; g < G; g++) {
            printf("%d %d\n", i * G + g, (k + j) * G + gmul(&bgr, g, s));
        }
    }
    return 0;
}
'''


C_SA = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NCAP 2600
#define WCAP 41   /* (NCAP + 63) / 64 */

static double wall_now(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

typedef struct { uint64_t s; } Rng;

static uint64_t rng_next(Rng *r) {
    uint64_t z = (r->s += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}
static int rng_int(Rng *r, int n) { return (int)(rng_next(r) % (uint64_t)n); }
static double rng_unit(Rng *r) { return (double)(rng_next(r) >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_, n, m;
static int side[NCAP], deg[NCAP], col[NCAP], qbuf[NCAP];
static int *adjv, *ea, *eb, *bea, *beb;
static int bn, bm, have;
static uint64_t *R, *T;

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_adj(int u, int v) {
    const int *row = adjv + (size_t)u * (size_t)d_;
    for (int i = 0; i < deg[u]; i++)
        if (row[i] == v) return 1;
    return 0;
}

static void add_adj(int u, int v) {
    adjv[(size_t)u * (size_t)d_ + deg[u]] = v;
    deg[u]++;
}

static void rem_adj(int u, int v) {
    int *row = adjv + (size_t)u * (size_t)d_;
    for (int i = 0; i < deg[u]; i++) {
        if (row[i] == v) {
            row[i] = row[deg[u] - 1];
            deg[u]--;
            return;
        }
    }
}

static void add_edge(int a, int b) { add_adj(a, b); add_adj(b, a); }
static void rem_edge(int a, int b) { rem_adj(a, b); rem_adj(b, a); }

/* Rebuild the A->B edge list from adjacency (A = side 0). */
static void rebuild_edges(void) {
    m = 0;
    for (int v = 0; v < n; v++) {
        if (side[v] != 0) continue;
        for (int i = 0; i < deg[v]; i++) {
            ea[m] = v;
            eb[m] = adjv[(size_t)v * (size_t)d_ + i];
            m++;
        }
    }
}

/* Degree-preserving bipartite 2-switch: (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). */
static int try_switch(Rng *r, int *oi, int *oj) {
    int i = rng_int(r, m), j = rng_int(r, m);
    if (i == j) return 0;
    int a1 = ea[i], b1 = eb[i], a2 = ea[j], b2 = eb[j];
    if (a1 == a2 || b1 == b2) return 0;
    if (has_adj(a1, b2) || has_adj(a2, b1)) return 0;
    rem_edge(a1, b1);
    rem_edge(a2, b2);
    add_edge(a1, b2);
    add_edge(a2, b1);
    ea[i] = a1; eb[i] = b2;
    ea[j] = a2; eb[j] = b1;
    *oi = i;
    *oj = j;
    return 1;
}

static void undo_switch(int i, int j) {
    int a1 = ea[i], b2 = eb[i], a2 = ea[j], b1 = eb[j];
    rem_edge(a1, b2);
    rem_edge(a2, b1);
    add_edge(a1, b1);
    add_edge(a2, b2);
    ea[i] = a1; eb[i] = b1;
    ea[j] = a2; eb[j] = b2;
}

/* Add two vertices (one A, one B). Take d_ edges (x_t, y_t) with distinct endpoints,
   remove them, and join a to every y_t and b to every x_t. Degrees stay d_. */
static int grow(Rng *r) {
    int xs[64], ys[64], cnt = 0, tries = 0;
    if (n + 2 > NCAP || m < d_) return 0;
    while (cnt < d_ && tries < 20000) {
        int i = rng_int(r, m);
        int x = ea[i], y = eb[i], ok = 1;
        tries++;
        for (int t = 0; t < cnt; t++) {
            if (xs[t] == x || ys[t] == y) { ok = 0; break; }
        }
        if (ok) {
            xs[cnt] = x;
            ys[cnt] = y;
            cnt++;
        }
    }
    if (cnt < d_) return 0;
    int a = n, b = n + 1;
    side[a] = 0;
    side[b] = 1;
    deg[a] = 0;
    deg[b] = 0;
    n += 2;
    for (int t = 0; t < cnt; t++) rem_edge(xs[t], ys[t]);
    for (int t = 0; t < cnt; t++) {
        add_edge(a, ys[t]);
        add_edge(xs[t], b);
    }
    rebuild_edges();
    return 1;
}

/* Sum over vertices of the number of vertices at distance > D_ (ordered pairs). 0 = valid. */
static long long cost_eval(void) {
    int W = (n + 63) >> 6;
    for (int v = 0; v < n; v++) {
        uint64_t *row = R + (size_t)v * WCAP;
        for (int w = 0; w < W; w++) row[w] = 0;
        row[v >> 6] |= 1ULL << (v & 63);
    }
    for (int lev = 0; lev < D_; lev++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = T + (size_t)v * WCAP;
            const uint64_t *src = R + (size_t)v * WCAP;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            const int *nb = adjv + (size_t)v * (size_t)d_;
            for (int e = 0; e < deg[v]; e++) {
                const uint64_t *su = R + (size_t)nb[e] * WCAP;
                for (int w = 0; w < W; w++) dst[w] |= su[w];
            }
        }
        uint64_t *tmp = R;
        R = T;
        T = tmp;
    }
    long long total = 0;
    for (int v = 0; v < n; v++) {
        const uint64_t *row = R + (size_t)v * WCAP;
        int c = 0;
        for (int w = 0; w < W; w++) c += popc64(row[w]);
        total += n - c;
    }
    return total;
}

static void save_best(void) {
    bn = n;
    bm = m;
    have = 1;
    memcpy(bea, ea, sizeof(int) * (size_t)m);
    memcpy(beb, eb, sizeof(int) * (size_t)m);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit   (graph on stdin)\n");
        return 1;
    }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tlim = atof(argv[4]);
    if (d_ < 2 || d_ > 64 || D_ < 2) {
        printf("0 0\n");
        return 0;
    }
    double deadline = wall_now() + tlim;
    Rng rng;
    rng.s = seed * 0x9E3779B97F4A7C15ULL + 0xABCDEFULL;

    adjv = malloc(sizeof(int) * (size_t)NCAP * (size_t)d_);
    ea = malloc(sizeof(int) * (size_t)NCAP * (size_t)d_);
    eb = malloc(sizeof(int) * (size_t)NCAP * (size_t)d_);
    bea = malloc(sizeof(int) * (size_t)NCAP * (size_t)d_);
    beb = malloc(sizeof(int) * (size_t)NCAP * (size_t)d_);
    R = calloc((size_t)NCAP * WCAP, sizeof(uint64_t));
    T = calloc((size_t)NCAP * WCAP, sizeof(uint64_t));
    if (!adjv || !ea || !eb || !bea || !beb || !R || !T) {
        printf("0 0\n");
        return 0;
    }

    int n0, m0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 < 2 || n0 > NCAP - 2 || m0 < 1) {
        printf("0 0\n");
        return 0;
    }
    n = n0;
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { printf("0 0\n"); return 0; }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v ||
            deg[u] >= d_ || deg[v] >= d_ || has_adj(u, v)) {
            printf("0 0\n");
            return 0;
        }
        add_adj(u, v);
        add_adj(v, u);
    }

    /* Bipartition by BFS 2-colouring. */
    for (int v = 0; v < n; v++) col[v] = -1;
    int qh = 0, qt = 0;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        qbuf[qt++] = s;
        while (qh < qt) {
            int v = qbuf[qh++];
            for (int e = 0; e < deg[v]; e++) {
                int u = adjv[(size_t)v * (size_t)d_ + e];
                if (col[u] < 0) {
                    col[u] = 1 - col[v];
                    qbuf[qt++] = u;
                } else if (col[u] == col[v]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }
    for (int v = 0; v < n; v++) side[v] = col[v];
    rebuild_edges();
    if (m != m0) {
        printf("0 0\n");
        return 0;
    }

    long long cur = cost_eval();
    if (cur == 0) save_best();

    while (wall_now() < deadline) {
        if (cur == 0) {
            save_best();
            if (!grow(&rng)) break;
            cur = cost_eval();
            continue;
        }
        double T0 = 1.0 + 3.0 * rng_unit(&rng);
        const long CH = 3000;
        for (long it = 0; it < CH; it++) {
            if ((it & 31) == 0 && wall_now() > deadline) break;
            double Tt = T0 * (1.0 - (double)it / (double)CH) + 0.15;
            int i = 0, j = 0;
            if (!try_switch(&rng, &i, &j)) continue;
            long long c2 = cost_eval();
            if (c2 <= cur || rng_unit(&rng) < exp(-(double)(c2 - cur) / Tt)) {
                cur = c2;
                if (cur == 0) break;
            } else {
                undo_switch(i, j);
            }
        }
    }
    if (cur == 0) save_best();

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", bn, bm);
    for (int i = 0; i < bm; i++) printf("%d %d\n", bea[i], beb[i]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Baseline constructions (always-valid fallbacks).
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

def build(d, D, seed, time_limit):
    start = time.monotonic()

    def left():
        return time_limit - (time.monotonic() - start)

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

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if best[0] >= lib.moore_bound(d, D):
        return best

    # Stage 1: group-voltage lift annealing (C_LIFT).
    lift_budget = max(1.0, 0.3 * time_limit - 1.0)
    try:
        out = lib.run_c(C_LIFT, [d, D, seed, f"{lift_budget:.2f}", best[0]],
                        timeout=lift_budget + 8.0)
        consider(*lib.parse_graph_text(out))
    except Exception:
        pass

    # Stage 2: full-graph 2-switch annealing with vertex growth (C_SA),
    # started from the best valid graph so far.
    sa_budget = left() - 9.0
    if sa_budget >= 2.0 and best[0] < lib.moore_bound(d, D):
        try:
            out = lib.run_c(C_SA, [d, D, seed, f"{sa_budget:.2f}"],
                            stdin_graph=best, timeout=sa_budget + 8.0)
            consider(*lib.parse_graph_text(out))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
