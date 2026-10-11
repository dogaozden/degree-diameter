import itertools

import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

/* Bi-Cayley search: vertices a_g (node g) and b_g (node G+g), edge a_g ~ b_{g s} for s in S, |S| = d.
   Left multiplication is an automorphism, so the diameter test only needs BFS from a_e and b_e.
   Groups: cyclic, semidirect Z_M x| Z_K (element a*K+b), and direct Z_M x Z_K. */

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
static long long powmod_ll(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

#define MAXG 1500

static int dd, DD, G;
static int gtype, gM, gK;
static int *pw = NULL, *mt = NULL, *iv = NULL, *S = NULL, *Sinv = NULL;
static int *inS = NULL, *mark = NULL, *queue = NULL;
static int stamp_ = 0;

static int gmul(int x, int y) {
    int a = x / gK, b = x % gK, c = y / gK, e = y % gK;
    if (gtype == 1) {
        long long t = ((long long)a + (long long)pw[b] * c) % gM;
        return (int)(t * gK + (b + e) % gK);
    }
    return ((a + c) % gM) * gK + (b + e) % gK;
}

static void set_group(int type, int M, int K, int r) {
    gtype = type;
    gM = M;
    gK = K;
    G = M * K;
    free(pw); free(mt); free(iv); free(inS); free(mark); free(queue);
    pw = malloc(sizeof(int) * (size_t)K);
    mt = malloc(sizeof(int) * (size_t)G * (size_t)G);
    iv = malloc(sizeof(int) * (size_t)G);
    inS = malloc(sizeof(int) * (size_t)G);
    mark = calloc((size_t)(2 * G), sizeof(int));
    queue = malloc(sizeof(int) * (size_t)(2 * G));
    stamp_ = 0;
    pw[0] = 1 % M;
    for (int b = 1; b < K; b++) pw[b] = (int)((long long)pw[b - 1] * r % M);
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            mt[(size_t)x * G + y] = gmul(x, y);
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            if (mt[(size_t)x * G + y] == 0) iv[x] = y;
}

/* Sum over the two base vertices of unreached vertices within distance DD. 0 means valid. */
static long long cost_eval(void) {
    long long total = 0;
    int N = 2 * G;
    for (int rep = 0; rep < 2; rep++) {
        int src = rep ? G : 0;
        int st = ++stamp_;
        int head = 0, tail = 0;
        queue[tail++] = src;
        mark[src] = st;
        for (int lev = 0; lev < DD && head < tail; lev++) {
            int end = tail;
            while (head < end) {
                int u = queue[head++];
                if (u < G) {
                    const int *row = mt + (size_t)u * G;
                    for (int i = 0; i < dd; i++) {
                        int v = G + row[S[i]];
                        if (mark[v] != st) { mark[v] = st; queue[tail++] = v; }
                    }
                } else {
                    const int *row = mt + (size_t)(u - G) * G;
                    for (int i = 0; i < dd; i++) {
                        int v = row[Sinv[i]];
                        if (mark[v] != st) { mark[v] = st; queue[tail++] = v; }
                    }
                }
            }
        }
        total += N - tail;
    }
    return total;
}

static long long anneal(Rng *rng, long iters, double deadline, int *bestS) {
    memset(inS, 0, sizeof(int) * (size_t)G);
    for (int i = 0; i < dd; i++) {
        int x;
        do { x = rng_int(rng, G); } while (inS[x]);
        inS[x] = 1;
        S[i] = x;
        Sinv[i] = iv[x];
    }
    long long cost = cost_eval();
    long long best = cost;
    memcpy(bestS, S, sizeof(int) * (size_t)dd);
    for (long it = 0; it < iters && best > 0; it++) {
        if ((it & 63) == 0 && wall_now() > deadline) break;
        double T = 2.0 * (1.0 - (double)it / (double)iters) + 0.05;
        int i = rng_int(rng, dd);
        int old = S[i];
        int x;
        do { x = rng_int(rng, G); } while (inS[x]);
        inS[old] = 0; inS[x] = 1; S[i] = x; Sinv[i] = iv[x];
        long long c2 = cost_eval();
        if (c2 <= cost || rng_unit(rng) < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
            if (cost < best) {
                best = cost;
                memcpy(bestS, S, sizeof(int) * (size_t)dd);
            }
        } else {
            inS[x] = 0; inS[old] = 1; S[i] = old; Sinv[i] = iv[old];
        }
    }
    return best;
}

static int sample_params(Rng *rng, int Gt, int *type, int *M, int *K, int *r) {
    int divs[512], nd = 0;
    for (int k = 2; k <= Gt / 2 && nd < 512; k++)
        if (Gt % k == 0) divs[nd++] = k;
    int c = rng_int(rng, 3);
    if (c == 0 || nd == 0) {
        *type = 1; *M = Gt; *K = 1; *r = 1;
        return 1;
    }
    if (c == 1) {
        for (int t = 0; t < 60; t++) {
            int k = divs[rng_int(rng, nd)];
            int m = Gt / k;
            int rr = 1 + rng_int(rng, m - 1);
            if (gcd_int(rr, m) == 1 && powmod_ll(rr, k, m) == 1 % m) {
                *type = 1; *M = m; *K = k; *r = rr;
                return 1;
            }
        }
        return 0;
    }
    int a = divs[rng_int(rng, nd)];
    *type = 2; *M = a; *K = Gt / a; *r = 0;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: prog d D seed time_limit n0\n");
        return 1;
    }
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tlim = atof(argv[4]);
    int n0 = atoi(argv[5]);
    if (dd < 2 || DD < 2 || dd > 64) {
        printf("0 0\n");
        return 0;
    }

    double deadline = wall_now() + tlim;
    Rng rng;
    rng.s = seed * 0x9E3779B97F4A7C15ULL + 0x5151ULL;

    S = malloc(sizeof(int) * (size_t)dd);
    Sinv = malloc(sizeof(int) * (size_t)dd);
    int *bestS = malloc(sizeof(int) * (size_t)dd);
    int *saveS = malloc(sizeof(int) * (size_t)dd);

    int bestG = n0 / 2;
    int have = 0, bt = 0, bM = 0, bK = 0, br = 0;

    while (wall_now() < deadline) {
        int Gt = bestG + 1 + rng_int(&rng, bestG / 12 + 2);
        if (Gt < dd + 1) Gt = dd + 1;
        if (Gt > MAXG) break;
        int t, M, K, r;
        if (!sample_params(&rng, Gt, &t, &M, &K, &r)) continue;
        set_group(t, M, K, r);
        long long res = anneal(&rng, 30000, deadline, bestS);
        if (res == 0) {
            bestG = G;
            have = 1;
            bt = t; bM = M; bK = K; br = r;
            memcpy(saveS, bestS, sizeof(int) * (size_t)dd);
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    set_group(bt, bM, bK, br);
    memcpy(S, saveS, sizeof(int) * (size_t)dd);
    for (int i = 0; i < dd; i++) Sinv[i] = iv[S[i]];
    printf("%d %d\n", 2 * G, G * dd);
    for (int g = 0; g < G; g++)
        for (int i = 0; i < dd; i++)
            printf("%d %d\n", g, G + mt[(size_t)g * G + S[i]]);
    return 0;
}
'''


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if best[0] >= lib.moore_bound(d, D):
        return best

    # Bi-Cayley connection-set search over groups of order above the current best.
    budget = max(1.0, 0.85 * time_limit - 4.0)
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", best[0]],
                        timeout=budget + 6.0)
        n, e = lib.parse_graph_text(out)
        consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
