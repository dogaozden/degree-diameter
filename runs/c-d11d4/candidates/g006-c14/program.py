import time

import lib

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define ITER_PER_ATTEMPT 1500

/* ---------------- RNG and clock ---------------- */
static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return n <= 1 ? 0 : (int)(rnd() % (uint64_t)n); }
static double rfrac(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double raw_now(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}
static double t_origin = 0.0;
static double now_s(void) { return raw_now() - t_origin; }

/* ---------------- semidirect group Z_m x| Z_k2, element a*k2+b ---------------- */
typedef struct {
    int m, k2, r, G;
    int *A, *B, *inv, *pw;
} Group;

static void group_free(Group *g) {
    free(g->A); free(g->B); free(g->inv); free(g->pw);
    g->A = g->B = g->inv = g->pw = NULL;
}

static void group_init(Group *g, int m, int k2, int r) {
    int G = m * k2;
    g->m = m; g->k2 = k2; g->r = r; g->G = G;
    g->pw = malloc(sizeof(int) * k2);
    g->A = malloc(sizeof(int) * G);
    g->B = malloc(sizeof(int) * G);
    g->inv = malloc(sizeof(int) * G);
    g->pw[0] = 1 % m;
    for (int b = 1; b < k2; b++) g->pw[b] = (int)((long long)g->pw[b - 1] * r % m);
    for (int x = 0; x < G; x++) { g->A[x] = x / k2; g->B[x] = x % k2; }
    for (int x = 0; x < G; x++) {
        int a = g->A[x], b = g->B[x];
        int nb = (k2 - b) % k2;
        int na = (m - (int)((long long)g->pw[nb] * a % m)) % m;
        g->inv[x] = na * k2 + nb;
    }
}

static inline int gmul(const Group *g, int x, int y) {
    int a1 = g->A[x], b1 = g->B[x], a2 = g->A[y], b2 = g->B[y];
    int aa = (int)(((long long)a1 + (long long)g->pw[b1] * a2) % g->m);
    int bb = b1 + b2;
    if (bb >= g->k2) bb -= g->k2;
    return aa * g->k2 + bb;
}

static int gcd_i(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
static int powmod_i(int b, int e, int m) {
    long long r = 1 % m, x = b % m;
    while (e > 0) { if (e & 1) r = r * x % m; x = x * x % m; e >>= 1; }
    return (int)r;
}

static Group grp;

static void choose_group(int G) {
    int divs[512], nd = 0;
    for (int k2 = 1; k2 <= G && nd < 512; k2++) if (G % k2 == 0) divs[nd++] = k2;
    int k2 = divs[rint_(nd)];
    int m = G / k2;
    int r = 1 % m;               /* direct product: always valid */
    if (m == 1) r = 0;
    else if (k2 > 1) {
        for (int t = 0; t < 60; t++) {
            int c = 1 + rint_(m - 1);
            if (gcd_i(c, m) == 1 && powmod_i(c, k2, m) == 1 % m) { r = c; break; }
        }
    }
    group_free(&grp);
    group_init(&grp, m, k2, r);
}

/* ---------------- lift state ---------------- */
/* Base: A vertices 0..K-1, B vertices K..2K-1. Lifted vertex id = base*G + x.
   Layer p is a permutation tg[p*K+i] of A index i to B index; voltage gv[p*K+i].
   Edge (A i, x) -- (B j, x*g). Left multiplication is an automorphism, so BFS
   from (u, identity) for each base u decides the diameter exactly. */
static int dd, DD, KK, GG;
static int *tg = NULL, *gv = NULL, *sB = NULL, *gB = NULL;
static int *dist_a = NULL, *stamp_a = NULL, *queue_a = NULL;
static int stamp_now = 0;

static int *btg = NULL, *bgv = NULL;
static int bK = 0, bG = 0, bm = 0, bk2 = 0, br = 0;
static int have_best = 0, best_n = 0;

static void rebuild_B(void) {
    for (int p = 0; p < dd; p++)
        for (int i = 0; i < KK; i++) {
            int j = tg[p * KK + i];
            sB[j * dd + p] = i;
            gB[j * dd + p] = grp.inv[gv[p * KK + i]];
        }
}

/* Returns the number of (base-representative, vertex) pairs at distance > D.
   Stops early and returns a value > cap once the running total exceeds cap. */
static long long evaluate(long long cap) {
    rebuild_B();
    const int K = KK, d = dd, D = DD, G = GG;
    const int n = 2 * K * G;
    long long cost = 0;
    for (int u = 0; u < 2 * K; u++) {
        stamp_now++;
        int head = 0, tail = 0;
        int s = u * G;
        stamp_a[s] = stamp_now; dist_a[s] = 0; queue_a[tail++] = s;
        int reached = 0;
        while (head < tail) {
            int v = queue_a[head++];
            int dv = dist_a[v];
            reached++;
            if (dv >= D) continue;
            int base = v / G, x = v - base * G;
            if (base < K) {
                for (int p = 0; p < d; p++) {
                    int j = tg[p * K + base];
                    int w = (K + j) * G + gmul(&grp, x, gv[p * K + base]);
                    if (stamp_a[w] != stamp_now) {
                        stamp_a[w] = stamp_now; dist_a[w] = dv + 1; queue_a[tail++] = w;
                    }
                }
            } else {
                int j = base - K;
                for (int p = 0; p < d; p++) {
                    int i = sB[j * d + p];
                    int w = i * G + gmul(&grp, x, gB[j * d + p]);
                    if (stamp_a[w] != stamp_now) {
                        stamp_a[w] = stamp_now; dist_a[w] = dv + 1; queue_a[tail++] = w;
                    }
                }
            }
        }
        cost += n - reached;
        if (cost > cap) return cost;
    }
    return cost;
}

static void free_lift(void) {
    free(tg); free(gv); free(sB); free(gB);
    free(dist_a); free(stamp_a); free(queue_a);
    tg = gv = sB = gB = NULL;
    dist_a = stamp_a = queue_a = NULL;
}

/* One hill-climb on voltages and layer targets for a random group of order G. */
static int run_attempt(int K, int G, int d, int D, int iters, double deadline) {
    KK = K; GG = G; dd = d; DD = D;
    choose_group(G);
    const int n = 2 * K * G;
    tg = malloc(sizeof(int) * K * d);
    gv = malloc(sizeof(int) * K * d);
    sB = malloc(sizeof(int) * K * d);
    gB = malloc(sizeof(int) * K * d);
    dist_a = malloc(sizeof(int) * n);
    stamp_a = calloc((size_t)n, sizeof(int));
    queue_a = malloc(sizeof(int) * n);
    int *perm = malloc(sizeof(int) * K);
    for (int p = 0; p < d; p++) {
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < K; i++) { tg[p * K + i] = perm[i]; gv[p * K + i] = rint_(G); }
    }
    free(perm);

    long long cur = evaluate(1LL << 60);
    for (int it = 0; it < iters && cur > 0; it++) {
        if (now_s() > deadline) break;
        long long cap = cur;
        if (rfrac() < 0.05) cap = cur + cur / 40 + 1;
        if (K >= 2 && rfrac() < 0.3) {
            int p = rint_(d), i = rint_(K), i2 = rint_(K - 1);
            if (i2 >= i) i2++;
            int a = p * K + i, b = p * K + i2;
            int t = tg[a]; tg[a] = tg[b]; tg[b] = t;
            long long c = evaluate(cap);
            if (c <= cap) cur = c;
            else { t = tg[a]; tg[a] = tg[b]; tg[b] = t; }
        } else {
            int idx = rint_(K * d);
            int old = gv[idx];
            gv[idx] = rint_(G);
            long long c = evaluate(cap);
            if (c <= cap) cur = c;
            else gv[idx] = old;
        }
    }
    int ok = (cur == 0);
    if (ok) {
        free(btg); free(bgv);
        btg = malloc(sizeof(int) * K * d);
        bgv = malloc(sizeof(int) * K * d);
        memcpy(btg, tg, sizeof(int) * K * d);
        memcpy(bgv, gv, sizeof(int) * K * d);
        bK = K; bG = G; bm = grp.m; bk2 = grp.k2; br = grp.r;
        best_n = n; have_best = 1;
    }
    free_lift();
    return ok;
}

static void output_best(int d) {
    int K = bK, G = bG, n = 2 * K * G;
    Group g;
    group_init(&g, bm, bk2, br);
    int cap = K * G * d;
    int *eu = malloc(sizeof(int) * cap);
    int *ev = malloc(sizeof(int) * cap);
    int *nb = malloc(sizeof(int) * d);
    int ne = 0;
    for (int i = 0; i < K; i++)
        for (int x = 0; x < G; x++) {
            int a = i * G + x, cnt = 0;
            for (int p = 0; p < d; p++) {
                int j = btg[p * K + i];
                int w = (K + j) * G + gmul(&g, x, bgv[p * K + i]);
                int dup = 0;
                for (int c = 0; c < cnt; c++) if (nb[c] == w) { dup = 1; break; }
                if (!dup) {
                    nb[cnt++] = w;
                    eu[ne] = a; ev[ne] = w; ne++;
                }
            }
        }
    printf("%d %d\n", n, ne);
    for (int e = 0; e < ne; e++) printf("%d %d\n", eu[e], ev[e]);
    free(eu); free(ev); free(nb);
    group_free(&g);
}

int main(int argc, char **argv) {
    int ch;
    while ((ch = getchar()) != EOF) { }
    t_origin = raw_now();
    if (argc < 5) { printf("0 0\n"); return 0; }
    const int d = atoi(argv[1]), D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    int t0 = argc > 5 ? atoi(argv[5]) : 2 * d;
    if (d < 2 || D < 2) { printf("0 0\n"); return 0; }
    rs = (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd();

    int tgt = t0 & ~1;
    if (tgt < 2) tgt = 2;
    int step = 2;
    while (now_s() < budget) {
        double rem = budget - now_s();
        double span = rem * 0.15 > 1.5 ? rem * 0.15 : 1.5;
        double slice_end = now_s() + span;
        if (slice_end > budget) slice_end = budget;
        int found = 0;
        while (now_s() < slice_end) {
            int Ks[6], nk = 0;
            for (int K = 1; K <= 6; K++) if (tgt % (2 * K) == 0) Ks[nk++] = K;
            int K = Ks[rint_(nk)];
            int G = tgt / (2 * K);
            if (run_attempt(K, G, d, D, ITER_PER_ATTEMPT, slice_end)) { found = 1; break; }
        }
        if (found) {
            step = step * 2 > 32 ? 32 : step * 2;
            tgt = best_n + step;
        } else if (!have_best) {
            int nt = (tgt * 9 / 10) & ~1;
            tgt = nt < 2 ? 2 : nt;
        } else {
            step = step / 2 < 2 ? 2 : step / 2;
            tgt = best_n + step;
        }
    }
    if (have_best) output_best(d);
    else printf("0 0\n");
    return 0;
}
"""


def _fallback(d):
    """K_{d,d}: valid for every D >= 2."""
    return lib.haar_graph(d, range(d))


def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # D = 3 with d-1 a prime power: the projective plane meets the Moore bound.
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        pg = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(pg[0], pg[1], d, D):
            return pg

    best = _fallback(d)

    if d >= 2:
        # Non-cyclic group lifts with a base of K+K vertices, searched by C.
        # The target starts near the record region and climbs as searches succeed.
        t0 = 1700 if (d, D) == (11, 4) else 2 * d
        budget = max(0.5, 0.8 * time_limit - 1.0 - (time.monotonic() - start))
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", t0],
                            timeout=budget + 5.0)
            n, e = lib.parse_graph_text(out)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = _fallback(d)
    return best
