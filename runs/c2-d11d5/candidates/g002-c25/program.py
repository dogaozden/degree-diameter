"""Bi-Cayley voltage-lift search for bipartite graphs with degree d and diameter D.

Changes in this version:
- The whole search runs in C (C_SOURCE). It is much faster than the Python loop, so
  annealing gets many more evaluations per second.
- The group family is wider: Z_m x| Z_k2 with direct products (r = 1), dihedral
  types, and general r with r^k2 = 1 mod m. Base sizes k = 1..6 are chosen by a bandit.
- Acceptance and defect targeting follow the earlier design, with more iterations
  and an iterated restart schedule.
- Python keeps a fallback at every step: K_{d,d} or PG(2,q). Each C result is
  checked with lib.is_valid before it is used. Any C failure falls back safely.
"""
import itertools
import time

import lib


C_SOURCE = r"""
#define _POSIX_C_SOURCE 199309L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXDEG 32
#define MAXK 6
#define PENALTY 1000L
#define ITERS 20000L
#define PATIENCE 3000L

typedef struct { int m, k2, G; int pw[64]; } Grp;

typedef struct {
    int k, d, D, G, N;
    Grp g;
    int lay[MAXDEG][MAXK];
    int S[MAXDEG][MAXK];
    int Si[MAXDEG][MAXK];
    int *nbr;               /* d * N, layer-major */
    uint32_t *reach, *cand, *bA, *bB;
} State;

static uint64_t rs = 88172645463325252ULL;
static unsigned char POP[1 << 16];
static double T0 = 0.0, TBUDGET = 1.0;
static int best_n = 0, best_m = 0;
static int *best_e = NULL;

static const int K2S[] = {1,1,2,2,3,4,5,6,7,8,9,10,12,14,16,18,20,24,30,36};
#define NK2 ((int)(sizeof K2S / sizeof K2S[0]))

static uint64_t rnd64(void) {
    rs ^= rs >> 12; rs ^= rs << 25; rs ^= rs >> 27;
    return rs * 2685821657736338717ULL;
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}
static int timeup(void) { return now() - T0 > TBUDGET; }

static int gcdi(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

static int gmul(const Grp *g, int x, int y) {
    int a = x / g->k2, b = x % g->k2, c = y / g->k2, e = y % g->k2;
    long long aa = ((long long)a + (long long)g->pw[b] * c) % g->m;
    return (int)aa * g->k2 + (b + e) % g->k2;
}

static int ginv(const Grp *g, int x) {
    int a = x / g->k2, b = x % g->k2;
    int nb = (g->k2 - b) % g->k2;
    long long t = ((long long)g->pw[nb] * a) % g->m;
    int ia = (int)((g->m - t) % g->m);
    return ia * g->k2 + nb;
}

/* Sample Z_m x| Z_k2 with order m*k2 >= target. Returns 1 on success. */
static int sample_group(int target, Grp *g) {
    for (int attempt = 0; attempt < 200; attempt++) {
        int k2 = K2S[rndint(NK2)];
        int m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        int r = -1;
        if (k2 == 1) {
            r = 1 % m;
        } else if (rnd01() < 0.2) {
            r = 1 % m;                      /* direct product */
        } else if (k2 == 2 && rnd01() < 0.3) {
            r = m - 1;                      /* dihedral type */
        } else {
            for (int t = 0; t < 80 && m > 2; t++) {
                int c = 2 + rndint(m - 2);
                if (gcdi(c, m) != 1) continue;
                long long p = 1;
                for (int j = 0; j < k2; j++) p = p * c % m;
                if (p == 1 % m) { r = c; break; }
            }
        }
        if (r < 0) continue;
        g->m = m; g->k2 = k2; g->G = m * k2;
        g->pw[0] = 1 % m;
        for (int t = 1; t < k2; t++) g->pw[t] = (int)((long long)g->pw[t - 1] * r % m);
        if ((long long)g->pw[k2 - 1] * r % m != 1 % m) continue;
        return 1;
    }
    return 0;
}

static void setdart(State *st, int l, int i) {
    int k = st->k, G = st->G, N = st->N;
    int p = st->lay[l][i], s = st->S[l][i], si = st->Si[l][i];
    int *nb = st->nbr + (size_t)l * (size_t)N;
    for (int x = 0; x < G; x++) {
        nb[i * G + x] = (k + p) * G + gmul(&st->g, x, s);
        nb[(k + p) * G + x] = i * G + gmul(&st->g, x, si);
    }
}

/* Returns the cost (unreached pairs + duplicate penalty). Writes the final reach mask to out. */
static long eval(State *st, uint32_t *out) {
    int k = st->k, G = st->G, N = st->N, d = st->d, D = st->D;
    uint32_t *cu = st->bA, *nx = st->bB;
    memset(cu, 0, sizeof(uint32_t) * (size_t)N);
    for (int b = 0; b < 2 * k; b++) cu[b * G] |= 1u << b;
    for (int step = 0; step < D; step++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint32_t x = cu[v];
            for (int l = 0; l < d; l++) x |= cu[st->nbr[(size_t)l * N + v]];
            nx[v] = x;
            if (x != cu[v]) changed = 1;
        }
        uint32_t *tmp = cu; cu = nx; nx = tmp;
        if (!changed) break;
    }
    long unr = 0;
    for (int v = 0; v < N; v++) {
        unr += 2 * k - POP[cu[v] & 0xFFFF];
        out[v] = cu[v];
    }
    long dup = 0;
    for (int i = 0; i < k; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (st->lay[l1][i] == st->lay[l2][i] && st->S[l1][i] == st->S[l2][i]) dup++;
    return unr + PENALTY * dup;
}

static int anneal(State *st) {
    int k = st->k, d = st->d, G = st->G, N = st->N;
    uint32_t full = (uint32_t)((1u << (2 * k)) - 1u);
    long cost = eval(st, st->reach);
    double c0 = cost > 0 ? (double)cost : 1.0;
    long best = cost, last = 0;
    for (long t = 0; t < ITERS && cost > 0; t++) {
        if (t - last > PATIENCE) break;
        if ((t & 31) == 0 && timeup()) break;
        double temp = 0.02 * c0 * (1.0 - (double)t / (double)ITERS);
        if (temp < 0.5) temp = 0.5;
        long c2;

        if (k >= 2 && rnd01() < 0.25) {
            /* Layer-swap move. */
            int l = rndint(d);
            int i1 = rndint(k), i2 = rndint(k - 1);
            if (i2 >= i1) i2++;
            int tmp = st->lay[l][i1]; st->lay[l][i1] = st->lay[l][i2]; st->lay[l][i2] = tmp;
            setdart(st, l, i1); setdart(st, l, i2);
            c2 = eval(st, st->cand);
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                memcpy(st->reach, st->cand, sizeof(uint32_t) * (size_t)N);
                if (cost < best) { best = cost; last = t; }
            } else {
                tmp = st->lay[l][i1]; st->lay[l][i1] = st->lay[l][i2]; st->lay[l][i2] = tmp;
                setdart(st, l, i1); setdart(st, l, i2);
            }
            continue;
        }

        /* Voltage move, defect-targeted with probability 0.4. */
        int l = -1, i = -1, v = -1;
        if (rnd01() < 0.4) {
            for (int tries = 0; tries < 40 && v < 0; tries++) {
                int u = rndint(N);
                if (st->reach[u] != full) v = u;
            }
        }
        if (v >= 0) {
            int block = v / G;
            l = rndint(d);
            if (block < k) {
                i = block;
            } else {
                for (int j = 0; j < k; j++) {
                    if (st->lay[l][j] == block - k) { i = j; break; }
                }
            }
            if (i < 0) continue;
        } else {
            l = rndint(d);
            i = rndint(k);
        }
        int old = st->S[l][i];
        int nw = rndint(G);
        if (nw == old) continue;
        st->S[l][i] = nw; st->Si[l][i] = ginv(&st->g, nw);
        setdart(st, l, i);
        c2 = eval(st, st->cand);
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            memcpy(st->reach, st->cand, sizeof(uint32_t) * (size_t)N);
            if (cost < best) { best = cost; last = t; }
        } else {
            st->S[l][i] = old; st->Si[l][i] = ginv(&st->g, old);
            setdart(st, l, i);
        }
    }
    return cost == 0;
}

static void store(State *st) {
    int k = st->k, d = st->d, N = st->N;
    int m = k * st->G * d;
    int *e = malloc(sizeof(int) * 2 * (size_t)m);
    if (!e) return;
    int c = 0;
    for (int u = 0; u < k * st->G; u++)
        for (int l = 0; l < d; l++) {
            e[2 * c] = u;
            e[2 * c + 1] = st->nbr[(size_t)l * N + u];
            c++;
        }
    free(best_e);
    best_e = e; best_m = m; best_n = N;
}

int main(int argc, char **argv) {
    char junk[4096];
    while (fread(junk, 1, sizeof junk, stdin) > 0) { }
    if (argc < 5) { printf("0 0\n"); return 0; }
    int d = atoi(argv[1]), D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    if (d < 3 || d > MAXDEG || D < 2 || budget <= 0) { printf("0 0\n"); return 0; }

    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int x = 0; x < (1 << 16); x++) {
        int c = 0, y = x;
        while (y) { c += y & 1; y >>= 1; }
        POP[x] = (unsigned char)c;
    }
    T0 = now();
    TBUDGET = budget;

    int trials[MAXK + 1], wins[MAXK + 1];
    for (int kk = 0; kk <= MAXK; kk++) { trials[kk] = 0; wins[kk] = 0; }

    while (!timeup()) {
        int k;
        if (rnd01() < 0.2) {
            k = 1 + rndint(MAXK);
        } else {
            double bv = -1.0;
            k = 1;
            for (int kk = 1; kk <= MAXK; kk++) {
                double v = (wins[kk] + 1.0) / (trials[kk] + 2.0) + 0.02 * rnd01();
                if (v > bv) { bv = v; k = kk; }
            }
        }
        int base = best_n / (2 * k);
        if (base < 1) base = 1;
        int spread = base / 8 + 1;
        if (spread < 2) spread = 2;
        int Gt = base + 1 + rndint(spread);

        Grp g;
        if (!sample_group(Gt, &g)) continue;
        int G = g.G;
        int N = 2 * k * G;
        if (N <= best_n) continue;

        State st;
        memset(&st, 0, sizeof st);
        st.k = k; st.d = d; st.D = D; st.G = G; st.N = N; st.g = g;
        st.nbr = malloc(sizeof(int) * (size_t)d * (size_t)N);
        st.reach = malloc(sizeof(uint32_t) * (size_t)N);
        st.cand = malloc(sizeof(uint32_t) * (size_t)N);
        st.bA = malloc(sizeof(uint32_t) * (size_t)N);
        st.bB = malloc(sizeof(uint32_t) * (size_t)N);
        if (!st.nbr || !st.reach || !st.cand || !st.bA || !st.bB) {
            free(st.nbr); free(st.reach); free(st.cand); free(st.bA); free(st.bB);
            break;
        }

        for (int l = 0; l < d; l++) {
            for (int i = 0; i < k; i++) st.lay[l][i] = i;
            for (int i = k - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int t = st.lay[l][i]; st.lay[l][i] = st.lay[l][j]; st.lay[l][j] = t;
            }
            for (int i = 0; i < k; i++) {
                st.S[l][i] = rndint(G);
                st.Si[l][i] = ginv(&st.g, st.S[l][i]);
                setdart(&st, l, i);
            }
        }

        trials[k]++;
        if (anneal(&st)) {
            wins[k]++;
            if (N > best_n) store(&st);
        }

        free(st.nbr); free(st.reach); free(st.cand); free(st.bA); free(st.bB);
    }

    if (best_n > 0 && best_e) {
        printf("%d %d\n", best_n, best_m);
        for (int e = 0; e < best_m; e++)
            printf("%d %d\n", best_e[2 * e], best_e[2 * e + 1]);
    } else {
        printf("0 0\n");
    }
    fflush(stdout);
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
    start = time.monotonic()
    tl = float(time_limit)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact construction for D = 3.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # The C search needs d >= 3 and D >= 3.
    if d < 3 or D < 3 or tl < 15.0:
        return best

    budget = max(1.0, min(0.8 * tl, tl - 12.0) - (time.monotonic() - start))
    if budget >= 2.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                            stdin_graph=None, timeout=budget + 5.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
