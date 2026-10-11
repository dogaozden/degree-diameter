import itertools
import math
import time

import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define BIGC 1000000000LL
#define MAXK 4

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
   Layer l = t / k holds a permutation i -> dJ, so every vertex has degree d. */
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

/* Simulated annealing. If warm != 0 the search starts from the darts already in st
   (a near-miss being polished) instead of a random lift. Returns the best cost found;
   the best darts are left in st->bestJ / st->bestS. */
static long long anneal(State *st, Rng *rng, long iters, double deadline, int warm, double T0) {
    int k = st->k, d = st->d, nd = st->nd, G = st->G;

    if (!warm) {
        for (int l = 0; l < d; l++) {
            int *p = st->dJ + l * k;
            for (int i = 0; i < k; i++) p[i] = i;
            for (int i = k - 1; i > 0; i--) {
                int j = rng_int(rng, i + 1);
                int tmp = p[i]; p[i] = p[j]; p[j] = tmp;
            }
        }
        for (int t = 0; t < nd; t++) st->dS[t] = rng_int(rng, G);
    }

    long long cost = eval_cost(st);
    long long best = cost;
    memcpy(st->bestS, st->dS, sizeof(int) * (size_t)nd);
    memcpy(st->bestJ, st->dJ, sizeof(int) * (size_t)nd);

    for (long it = 0; it < iters && best > 0; it++) {
        if ((it & 255) == 0 && wall_now() > deadline) break;
        double T = T0 * (1.0 - (double)it / (double)iters) + 0.05;
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

    int maxnd = MAXK * d;
    int *outJ = xmalloc(sizeof(int) * (size_t)maxnd);
    int *outS = xmalloc(sizeof(int) * (size_t)maxnd);
    int *nmJ = xmalloc(sizeof(int) * (size_t)maxnd);
    int *nmS = xmalloc(sizeof(int) * (size_t)maxnd);
    int have = 0, best_n = n0, bk = 0, bG = 0;
    Group bgr;
    memset(&bgr, 0, sizeof(bgr));

    /* Near-miss: the lowest-cost failing lift whose order beats the current best.
       It is polished later by a warm-started anneal at the same group (new idea). */
    int have_nm = 0, nmk = 0, nmG = 0;
    long long nmcost = BIGC;
    Group nmgr;
    memset(&nmgr, 0, sizeof(nmgr));

    while (wall_now() < deadline) {
        int use_warm = have_nm && (rng_unit(&rng) < 0.5);
        int k, G;
        Group gr;
        long long res;
        State st;

        if (use_warm) {
            k = nmk;
            G = nmG;
            gr = nmgr;
            state_init(&st, d, D, k, G, &gr);
            memcpy(st.dJ, nmJ, sizeof(int) * (size_t)(d * k));
            memcpy(st.dS, nmS, sizeof(int) * (size_t)(d * k));
            res = anneal(&st, &rng, 30000, deadline, 1, 0.6);
        } else {
            int r = rng_int(&rng, 7);
            k = (r < 2) ? 1 : ((r < 4) ? 2 : ((r < 6) ? 3 : 4));
            int base = best_n / (2 * k);
            int spread = base / 6 + 2;
            G = base + 1 + rng_int(&rng, spread);
            if (G < 2) G = 2;
            if (!sample_group(&rng, G, &gr)) continue;
            state_init(&st, d, D, k, G, &gr);
            res = anneal(&st, &rng, 40000, deadline, 0, 3.0);
        }

        int n = 2 * k * G;
        if (res == 0) {
            if (n > best_n) {
                best_n = n;
                have = 1;
                bk = k;
                bG = G;
                bgr = gr;
                memcpy(outJ, st.bestJ, sizeof(int) * (size_t)st.nd);
                memcpy(outS, st.bestS, sizeof(int) * (size_t)st.nd);
                have_nm = 0;   /* near-misses at old orders are now stale */
            }
        } else if (n > best_n && (!have_nm || res < nmcost)) {
            have_nm = 1;
            nmk = k;
            nmG = G;
            nmgr = gr;
            nmcost = res;
            memcpy(nmJ, st.bestJ, sizeof(int) * (size_t)st.nd);
            memcpy(nmS, st.bestS, sizeof(int) * (size_t)st.nd);
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


def build(d, D, seed, time_limit):
    start = time.monotonic()

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

    # Already at the Moore bound: nothing to search for.
    if best[0] >= lib.moore_bound(d, D):
        return best

    # Main search: C engine (random voltage lifts over k <= 4 base vertices,
    # plus warm-started polishing of near-miss lifts), seeded with the best baseline.
    budget = max(1.0, 0.8 * time_limit - 3.0)
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", best[0]],
                        timeout=budget + 8.0)
        n, e = lib.parse_graph_text(out)
        consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

