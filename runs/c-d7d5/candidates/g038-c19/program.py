import time

import lib


# ----------------------------------------------------------------------------
# Exact baseline: incidence graph of PG(2, q) for the largest prime power q
# with q + 1 <= d. Valid for diameter 3.
# ----------------------------------------------------------------------------

def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# C engine: simulated annealing over bi-Cayley lifts (voltage assignments on
# semidirect groups Z_m x| Z_k). Each attempt picks a random base size K in
# {1,2,3} and a group of order G with 2KG just above the current best order,
# then anneals darts to zero unreached pairs. Vertices: A_{i,g} = i*G+g,
# B_{j,h} = (K+j)*G+h; dart (l,i) joins A_{i,g} to B_{P[l][i], g*S[l][i]}.
# Left translations are automorphisms, so BFS from one root per base vertex
# is enough. Energy = unreached root-pairs + PEN * duplicate darts.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 16
#define MAXK 3
#define PEN 20
#define T0 2.0
#define T1 0.2

typedef struct {
    int P[MAXD][MAXK];
    int S[MAXD][MAXK];
} Cfg;

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int ri(int n) { return (int)(rnd() % (uint64_t)n); }

static double rf(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int Dd = 3, DD = 3;
static double deadline = 0.0;
static int GM = 1, GK = 1, GG = 1;
static int gpow[64];

static void set_group(int m, int k, int r) {
    GM = m;
    GK = k;
    GG = m * k;
    long long p = 1 % m;
    for (int b = 0; b < k; b++) {
        gpow[b] = (int)p;
        p = (p * r) % m;
    }
}

/* Semidirect product Z_m x| Z_k, element (a,b) coded as a*k+b; identity is 0. */
static int gmul(int x, int y) {
    int a = x / GK, b = x % GK;
    int c = y / GK, d = y % GK;
    long long t = ((long long)a + (long long)gpow[b] * (long long)c) % GM;
    return (int)t * GK + (b + d) % GK;
}

static int *adj = NULL, *vis = NULL, *qu = NULL, *cntb = NULL;
static int capN = 0, stamp = 0;

static void ensure(int N) {
    if (N <= capN) return;
    free(adj);
    free(vis);
    free(qu);
    free(cntb);
    capN = N;
    adj = malloc(sizeof(int) * (size_t)N * MAXD);
    vis = calloc((size_t)N, sizeof(int));
    qu = malloc(sizeof(int) * (size_t)N);
    cntb = malloc(sizeof(int) * (size_t)N);
    stamp = 0;
    if (!adj || !vis || !qu || !cntb) {
        fprintf(stderr, "out of memory\n");
        exit(1);
    }
}

static long long eval_cost(const Cfg *c, int K, int G) {
    int N = 2 * K * G;
    ensure(N);
    memset(cntb, 0, sizeof(int) * (size_t)N);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = c->P[l][i], s = c->S[l][i];
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                int b = (K + j) * G + gmul(g, s);
                adj[a * MAXD + cntb[a]++] = b;
                adj[b * MAXD + cntb[b]++] = a;
            }
        }
    }
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < Dd; l1++)
            for (int l2 = l1 + 1; l2 < Dd; l2++)
                if (c->P[l1][i] == c->P[l2][i] && c->S[l1][i] == c->S[l2][i])
                    dup++;

    long long raw = 0;
    for (int r = 0; r < 2 * K; r++) {
        stamp++;
        int head = 0, tail = 0, src = r * G;
        vis[src] = stamp;
        qu[tail++] = src;
        for (int lvl = 0; lvl < DD && head < tail; lvl++) {
            int end = tail;
            while (head < end) {
                int u = qu[head++];
                for (int t = 0; t < Dd; t++) {
                    int v = adj[u * MAXD + t];
                    if (vis[v] != stamp) {
                        vis[v] = stamp;
                        qu[tail++] = v;
                    }
                }
            }
        }
        raw += N - tail;
    }
    return raw + (long long)PEN * dup;
}

static void rand_cfg(Cfg *c, int K) {
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) c->P[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = ri(i + 1);
            int t = c->P[l][i];
            c->P[l][i] = c->P[l][j];
            c->P[l][j] = t;
        }
        for (int i = 0; i < K; i++) c->S[l][i] = ri(GG);
    }
}

/* Simulated annealing with a time-based geometric cooling schedule. */
static long long anneal(int K, double dur, Cfg *out) {
    Cfg cur, cand, best;
    rand_cfg(&cur, K);
    long long E = eval_cost(&cur, K, GG);
    long long bestE = E;
    best = cur;
    double t0 = now_s();
    double T = T0;
    for (long long it = 0; E > 0; it++) {
        if ((it & 63) == 0) {
            double now = now_s();
            if (now > deadline || now - t0 > dur) break;
            double f = (now - t0) / dur;
            T = T0 * pow(T1 / T0, f);
        }
        cand = cur;
        int l = ri(Dd), i = ri(K);
        if (K >= 2 && ri(3) == 0) {
            int i2 = ri(K - 1);
            if (i2 >= i) i2++;
            int t = cand.P[l][i];
            cand.P[l][i] = cand.P[l][i2];
            cand.P[l][i2] = t;
        } else {
            cand.S[l][i] = ri(GG);
        }
        long long E2 = eval_cost(&cand, K, GG);
        long long dE = E2 - E;
        if (dE <= 0 || rf() < exp(-(double)dE / T)) {
            cur = cand;
            E = E2;
            if (E < bestE) {
                bestE = E;
                best = cur;
            }
        }
    }
    *out = best;
    return bestE;
}

static long long gcdll(long long a, long long b) {
    while (b) {
        long long t = a % b;
        a = b;
        b = t;
    }
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

/* Pick a group of order G: a random divisor k, then r with r^k = 1 mod m. */
static void pick_group(int G, int *om, int *ok, int *orr) {
    int divs[64], nd = 0;
    for (int k = 1; k <= 64 && k <= G; k++)
        if (G % k == 0) divs[nd++] = k;
    for (int t = 0; t < 60; t++) {
        int k = divs[ri(nd)];
        int m = G / k;
        if (k == 1) break;
        if (m < 2) continue;
        for (int u = 0; u < 400; u++) {
            int r = 1 + ri(m - 1);
            if (gcdll(r, m) == 1 && powmod(r, k, m) == 1 % m) {
                *om = m;
                *ok = k;
                *orr = r;
                return;
            }
        }
    }
    *om = G;
    *ok = 1;
    *orr = 1;
}

int main(int argc, char **argv) {
    Dd = argc > 1 ? atoi(argv[1]) : 3;
    DD = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;
    long long min_n = argc > 5 ? atoll(argv[5]) : 0;

    if (Dd < 1 || Dd > MAXD || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 8; w++) rnd();

    deadline = now_s() + tl;
    long long best_n = min_n;
    int have = 0;
    Cfg bestcfg;
    memset(&bestcfg, 0, sizeof(bestcfg));
    int bK = 1, bM = 1, bk = 1, br = 1;

    while (1) {
        double remain = deadline - now_s();
        if (remain < 0.5) break;

        int K = 1 + ri(3);
        long long span = best_n / 40 + 3;
        long long T = best_n + 1 + (long long)ri((int)span);
        long long G = (T + 2LL * K - 1) / (2LL * K);
        if (2LL * K * G <= best_n) G = best_n / (2LL * K) + 1;
        if (G < 2) G = 2;
        if (G > 3000) continue;

        int m, k, r;
        pick_group((int)G, &m, &k, &r);
        set_group(m, k, r);
        if (2 * K * GG <= best_n) continue;

        double dur = remain / 4.0;
        if (dur < 1.5) dur = 1.5;
        if (dur > 12.0) dur = 12.0;

        Cfg cand;
        long long E = anneal(K, dur, &cand);
        if (E == 0) {
            best_n = 2LL * K * GG;
            have = 1;
            bestcfg = cand;
            bK = K;
            bM = m;
            bk = k;
            br = r;
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    set_group(bM, bk, br);
    int K = bK, G = GG;
    int n = 2 * K * G;
    long nedges = (long)Dd * K * G;
    printf("%d %ld\n", n, nedges);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = bestcfg.P[l][i], s = bestcfg.S[l][i];
            for (int g = 0; g < G; g++) {
                printf("%d %d\n", i * G + g, (K + j) * G + gmul(g, s));
            }
        }
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions and fallbacks first, then the C search.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        try:
            if n > best_n and lib.is_valid(n, e, d, D):
                best = (n, e)
                best_n = n
        except Exception:
            pass

    if D >= 3:
        try:
            pg = _best_pg(d)
        except Exception:
            pg = None
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Annealing over bi-Cayley lifts, seeded with the best order so far.
    if 3 <= d <= 16 and D >= 3:
        budget = min(0.8 * time_limit, time_limit - 8.0)
        if budget >= 3.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", best_n],
                                timeout=time_limit - 4.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
