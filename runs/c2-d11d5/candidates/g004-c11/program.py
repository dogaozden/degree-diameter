"""Haar-graph search (cyclic difference sets) followed by a bi-Cayley annealing stage.

Construction: the Haar graph H(Z_m, S) has parts A_x and B_y with A_x ~ B_{x+s} for s in S,
|S| = d. It is bipartite and d-regular on 2m vertices. Translation symmetry reduces the
diameter test to two BFS runs, one from A_0 and one from B_0. The C engine anneals over
the d-element set S for each m, and walks m upward with an adaptive step. A bi-Cayley
annealer (the previous program's engine) then uses the remaining budget and only keeps
graphs larger than the Haar result. Every kept graph is checked with lib.is_valid. The
fallbacks are K_{d,d}, and PG(2,q) when D = 3.
"""
import time

import lib


C_HAAR = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;
#define MAXDEG 64

static u64 rs;
static u64 rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static int rndint(int n) { int v = (int)(rndu() * (double)n); return v >= n ? n - 1 : v; }
static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int DEG, DIAM, M;
static int S[MAXDEG];
static unsigned char *bufA = NULL, *bufB = NULL, *bufC = NULL, *bufD = NULL;
static unsigned char *RA, *RB, *NA, *NB;
static int cap = 0;

static void ensure_cap(int m) {
    if (m <= cap) return;
    free(bufA); free(bufB); free(bufC); free(bufD);
    bufA = malloc((size_t)m); bufB = malloc((size_t)m);
    bufC = malloc((size_t)m); bufD = malloc((size_t)m);
    if (!bufA || !bufB || !bufC || !bufD) { printf("0 0\n"); exit(0); }
    cap = m;
    RA = bufA; RB = bufB; NA = bufC; NB = bufD;
}

/* Number of unreached (A or B) residues within DIAM steps of A_0 (src 0) or B_0 (src 1). */
static int unreached_from(int src) {
    int m = M;
    memset(RA, 0, (size_t)m);
    memset(RB, 0, (size_t)m);
    if (src == 0) RA[0] = 1; else RB[0] = 1;
    for (int t = 0; t < DIAM; t++) {
        memcpy(NA, RA, (size_t)m);
        memcpy(NB, RB, (size_t)m);
        int changed = 0;
        for (int j = 0; j < DEG; j++) {
            int s = S[j];
            for (int x = 0; x < m; x++) {
                if (RA[x]) {            /* A_x ~ B_{x+s} */
                    int y = x + s; if (y >= m) y -= m;
                    if (!NB[y]) { NB[y] = 1; changed = 1; }
                }
                if (RB[x]) {            /* B_x ~ A_{x-s} */
                    int y = x - s; if (y < 0) y += m;
                    if (!NA[y]) { NA[y] = 1; changed = 1; }
                }
            }
        }
        unsigned char *tmp;
        tmp = RA; RA = NA; NA = tmp;
        tmp = RB; RB = NB; NB = tmp;
        if (!changed) break;
    }
    int unr = 0;
    for (int x = 0; x < m; x++) { unr += !RA[x]; unr += !RB[x]; }
    return unr;
}

static int cost(void) { return unreached_from(0) + unreached_from(1); }

static int attempt(int m, long iters, double deadline, int *outS) {
    M = m;
    ensure_cap(m);
    int cur[MAXDEG];
    for (int j = 0; j < DEG; j++) {
        int v;
        for (;;) {
            v = rndint(m);
            int ok = 1;
            for (int i = 0; i < j; i++) if (cur[i] == v) { ok = 0; break; }
            if (ok) break;
        }
        cur[j] = v;
    }
    memcpy(S, cur, sizeof(int) * (size_t)DEG);
    int c = cost();
    for (long t = 0; t < iters && c > 0; t++) {
        if ((t & 31) == 0 && now() > deadline) break;
        double T = 1.5 * (1.0 - (double)t / (double)iters) + 0.1;
        int j = rndint(DEG);
        int old = S[j];
        int v;
        for (;;) {
            v = rndint(m);
            int ok = 1;
            for (int i = 0; i < DEG; i++) if (S[i] == v) { ok = 0; break; }
            if (ok) break;
        }
        S[j] = v;
        int c2 = cost();
        if (c2 <= c || rndu() < exp(-(double)(c2 - c) / T)) c = c2;
        else S[j] = old;
    }
    if (c == 0) {
        memcpy(outS, S, sizeof(int) * (size_t)DEG);
        return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    long m0 = argc > 5 ? atol(argv[5]) : 0;
    if (d < 2 || d > MAXDEG || D < 2) { printf("0 0\n"); return 0; }
    DEG = d;
    DIAM = D;
    rs = 0x9E3779B97F4A7C15ULL ^ ((u64)seed * 0x2545F4914F6CDD1DULL + 99991ULL);
    if (rs == 0) rs = 1;
    for (int w = 0; w < 12; w++) rnd64();

    double deadline = now() + tl;
    if (m0 < d + 1) m0 = d + 1;

    int best_m = 0;
    int bestS[MAXDEG];
    int outS[MAXDEG];
    long try_m = m0, step = 16, iters = 4000;

    while (now() < deadline) {
        int ok = attempt((int)try_m, iters, deadline, outS);
        if (ok) {
            best_m = (int)try_m;
            memcpy(bestS, outS, sizeof(int) * (size_t)DEG);
            step *= 2;
            if (step > 1024) step = 1024;
            try_m = best_m + step;
        } else if (best_m > 0) {
            if (step > 1) step /= 2;
            try_m = best_m + step;
            if (step == 1 && iters < 200000) iters *= 2;
        } else {
            long nt = try_m - step;
            try_m = nt > d ? nt : d + 1;
            step *= 2;
        }
    }

    if (best_m == 0) {
        printf("0 0\n");
        return 0;
    }
    int m = best_m;
    printf("%d %d\n", 2 * m, m * DEG);
    for (int x = 0; x < m; x++)
        for (int j = 0; j < DEG; j++) {
            int y = x + bestS[j];
            if (y >= m) y -= m;
            printf("%d %d\n", x, m + y);
        }
    return 0;
}
'''


C_BICAYLEY = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 64
#define MAXK 8
#define PENALTY 1000

typedef uint64_t u64;

static u64 rs;
static u64 rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static int rndint(int n) { int v = (int)(rndu() * n); return v >= n ? n - 1 : v; }

static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int pc64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static long long gcdll(long long a, long long b) {
    while (b) { long long t = a % b; a = b; b = t; }
    return a;
}

static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

typedef struct { int m, k2, G; long long r; int pw[64]; } Group;
static Group grp;

static void set_group(int m, int k2, long long r) {
    grp.m = m; grp.k2 = k2; grp.G = m * k2; grp.r = r;
    long long p = 1 % m;
    for (int b = 0; b < k2; b++) { grp.pw[b] = (int)p; p = (p * r) % m; }
}

static int gmul(int x, int y) {
    int k2 = grp.k2, m = grp.m;
    int a = x / k2, b = x % k2, c = y / k2, e = y % k2;
    long long t = (a + (long long)grp.pw[b] * c) % m;
    return (int)(t * k2 + (b + e) % k2);
}

static int ginv(int x) {
    int k2 = grp.k2, m = grp.m;
    int a = x / k2, b = x % k2;
    int nb = (k2 - b) % k2;
    long long t = ((long long)grp.pw[nb] * a) % m;
    long long na = (m - t) % m;
    return (int)(na * k2 + nb);
}

static int DEG, D_, K, G, N;
static int layers[MAXD][MAXK];
static int S[MAXD][MAXK];
static int *nbr = NULL;
static u64 *ra = NULL, *rb = NULL;
static u64 FULL;

static int best_n = 0, best_m = 0;
static int *best_e = NULL;

static void set_dart(int l, int i) {
    int p = layers[l][i], s = S[l][i];
    int sinv = ginv(s);
    int *nl = nbr + (size_t)l * N;
    int q = K + p;
    for (int g = 0; g < G; g++) nl[i * G + g] = q * G + gmul(g, s);
    for (int h = 0; h < G; h++) nl[q * G + h] = i * G + gmul(h, sinv);
}

static int reach_eval(void) {
    for (int v = 0; v < N; v++) ra[v] = 0;
    for (int b = 0; b < 2 * K; b++) ra[b * G] |= (u64)1 << b;
    for (int round = 0; round < D_; round++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            u64 u = ra[v];
            for (int l = 0; l < DEG; l++) u |= ra[nbr[(size_t)l * N + v]];
            rb[v] = u;
            if (u != ra[v]) changed = 1;
        }
        u64 *t = ra; ra = rb; rb = t;
        if (!changed) break;
    }
    int unr = 0;
    for (int v = 0; v < N; v++) unr += pc64(FULL & ~ra[v]);
    return unr;
}

static long long eval_cost(void) {
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < DEG; l++)
            for (int l2 = l + 1; l2 < DEG; l2++)
                if (layers[l][i] == layers[l2][i] && S[l][i] == S[l2][i]) dup++;
    int unr = reach_eval();
    return (long long)unr + (long long)PENALTY * dup;
}

static void record_solution(void) {
    int m = K * G * DEG;
    int *e = malloc(sizeof(int) * 2 * (size_t)m);
    if (!e) return;
    int idx = 0;
    for (int u = 0; u < K * G; u++)
        for (int l = 0; l < DEG; l++) {
            e[2 * idx] = u;
            e[2 * idx + 1] = nbr[(size_t)l * N + u];
            idx++;
        }
    free(best_e);
    best_e = e;
    best_m = m;
    best_n = N;
}

static int anneal(long iters, long patience, double deadline) {
    long long cost = eval_cost();
    double c0 = cost > 1 ? (double)cost : 1.0;
    long long bestc = cost;
    long last = 0;
    for (long t = 0; t < iters; t++) {
        if (cost == 0) return 1;
        if (now() > deadline) break;
        if (t - last > patience) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;

        if (K >= 2 && rndu() < 0.25) {
            int l = rndint(DEG);
            int i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int tmp = layers[l][i1]; layers[l][i1] = layers[l][i2]; layers[l][i2] = tmp;
            set_dart(l, i1); set_dart(l, i2);
            long long c2 = eval_cost();
            if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                if (cost < bestc) { bestc = cost; last = t; }
            } else {
                tmp = layers[l][i1]; layers[l][i1] = layers[l][i2]; layers[l][i2] = tmp;
                set_dart(l, i1); set_dart(l, i2);
            }
            continue;
        }

        int l = -1, i = -1;
        if (rndu() < 0.4) {
            for (int tries = 0; tries < 30 && l < 0; tries++) {
                int v = rndint(N);
                if ((ra[v] & FULL) != FULL) {
                    int block = v / G;
                    if (block < K) {
                        i = block;
                        l = rndint(DEG);
                    } else {
                        l = rndint(DEG);
                        for (int j = 0; j < K; j++)
                            if (layers[l][j] == block - K) { i = j; break; }
                    }
                }
            }
        }
        if (l < 0) { l = rndint(DEG); i = rndint(K); }

        int old = S[l][i];
        int nw = rndint(G);
        if (nw == old) continue;
        S[l][i] = nw;
        set_dart(l, i);
        long long c2 = eval_cost();
        if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            if (cost < bestc) { bestc = cost; last = t; }
        } else {
            S[l][i] = old;
            set_dart(l, i);
        }
    }
    return cost == 0;
}

static const int K2LIST[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};

static int sample_group(int target, int *pm, int *pk2, long long *pr) {
    for (int tries = 0; tries < 200; tries++) {
        int k2 = K2LIST[rndint(20)];
        int m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        long long r = -1;
        if (k2 == 1) {
            r = 1;
        } else if (k2 == 2 && rndu() < 0.3) {
            r = m - 1;
        } else {
            if (m > 2) {
                for (int t = 0; t < 60; t++) {
                    long long c = 2 + rndint(m - 2);
                    if (gcdll(c, m) == 1 && powmod(c, k2, m) == 1 % m) { r = c; break; }
                }
            } else {
                r = 1;
            }
            if (r < 0) continue;
        }
        *pm = m; *pk2 = k2; *pr = r;
        return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int n0 = argc > 5 ? atoi(argv[5]) : 0;
    if (d < 2 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }
    DEG = d;
    D_ = D;
    rs = 0x9E3779B97F4A7C15ULL ^ (u64)(seed * 2654435761UL + 12345UL);
    if (rs == 0) rs = 1;
    for (int w = 0; w < 10; w++) rnd64();

    double start = now(), deadline = start + tl;
    best_n = n0;
    best_m = 0;
    best_e = NULL;
    int trials[MAXK + 1] = {0}, wins[MAXK + 1] = {0};

    while (now() < deadline) {
        int k;
        if (rndu() < 0.2) {
            k = 1 + rndint(MAXK);
        } else {
            double bs = -1.0;
            k = 1;
            for (int kk = 1; kk <= MAXK; kk++) {
                double s = (wins[kk] + 1.0) / (trials[kk] + 2.0) + 0.02 * rndu();
                if (s > bs) { bs = s; k = kk; }
            }
        }
        int base = best_n / (2 * k);
        int spread = base / 8 + 1;
        int target = base + 1 + rndint(spread);
        if (target < 2) target = 2;

        int m, k2;
        long long r;
        if (!sample_group(target, &m, &k2, &r)) continue;
        set_group(m, k2, r);
        G = grp.G;
        K = k;
        N = 2 * K * G;
        if (N <= best_n) continue;

        FULL = (((u64)1) << (2 * K)) - 1;
        nbr = malloc(sizeof(int) * (size_t)DEG * N);
        ra = malloc(sizeof(u64) * (size_t)N);
        rb = malloc(sizeof(u64) * (size_t)N);
        if (!nbr || !ra || !rb) {
            free(nbr); free(ra); free(rb);
            nbr = NULL; ra = NULL; rb = NULL;
            break;
        }

        for (int l = 0; l < DEG; l++) {
            for (int i = 0; i < K; i++) layers[l][i] = i;
            for (int i = K - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int tmp = layers[l][i]; layers[l][i] = layers[l][j]; layers[l][j] = tmp;
            }
        }
        for (int l = 0; l < DEG; l++)
            for (int i = 0; i < K; i++) S[l][i] = rndint(G);
        for (int l = 0; l < DEG; l++)
            for (int i = 0; i < K; i++) set_dart(l, i);

        trials[K]++;
        int ok = anneal(8000, 1500, deadline);
        if (ok) {
            wins[K]++;
            record_solution();
        }
        free(nbr); free(ra); free(rb);
        nbr = NULL; ra = NULL; rb = NULL;
    }

    if (best_m == 0) {
        printf("0 0\n");
    } else {
        printf("%d %d\n", best_n, best_m);
        for (int j = 0; j < best_m; j++)
            printf("%d %d\n", best_e[2 * j], best_e[2 * j + 1]);
    }
    return 0;
}
'''


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    best = (2 * d, [(i, d + j) for i in range(d) for j in range(d)])
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact construction for D = 3 when d - 1 is a prime power.
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        if lib.is_prime_power(d - 1):
            return best

    total = max(1.0, 0.85 * time_limit - 3.0)
    deadline = start + total

    # Stage 1: Haar graph H(Z_m, S) with S of size d; search S for the largest m.
    haar_budget = 0.5 * total
    try:
        out = lib.run_c(C_HAAR, [d, D, seed, round(haar_budget, 2), d + 1],
                        stdin_graph=None, timeout=haar_budget + 6.0)
        n, e = lib.parse_graph_text(out)
        consider(n, e)
    except Exception:
        pass

    # Stage 2: bi-Cayley annealing, seeded so it only keeps graphs larger than the current best.
    remaining = deadline - time.monotonic()
    if remaining > 3.0 and 2 <= d <= 64:
        try:
            out = lib.run_c(C_BICAYLEY, [d, D, seed, round(0.9 * remaining, 2), best[0]],
                            stdin_graph=None, timeout=remaining + 6.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = (2 * d, [(i, d + j) for i in range(d) for j in range(d)])
    return best
