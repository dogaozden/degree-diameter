"""Cayley-bipartite search over metacyclic (semidirect) groups, Frobenius groups included.

Construction (C engine):
  For a group G of order n and a connection set S of d elements containing the identity,
  the bipartite graph on G x {0,1} with edges (g,0)-(g s,1) for s in S is d-regular and has
  2n vertices. Left multiplication is an automorphism on each side, so the diameter is at
  most D iff BFS from (e,0) and from (e,1) reach everything within D steps. Each cost
  evaluation is therefore two BFS runs.

  Groups: Z_m x|_r Z_k (element a*k+b). This includes AGL(1,p) = Z_p x| Z_{p-1}, which the
  previous engine never tried because it capped the cyclic-part order at 12. The order n is
  swept upward from a low start. Each candidate group gets a simulated-annealing run on S,
  with the number of unreached (source, vertex) pairs as cost. On success the order rises
  to n+1, so the search keeps climbing.

Python glue: known constructions for D = 3, K_{d,d} as a valid fallback, and final
validation with lib.is_valid. Only a strictly larger valid graph replaces the fallback.
"""
import time

import lib

C_SOURCE = r"""
#define _POSIX_C_SOURCE 200809L
#include <limits.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXDEG 64

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rs[2];

static uint64_t splitmix(uint64_t *x) {
    uint64_t z = (*x += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

static uint64_t rnd64(void) {
    uint64_t s1 = rs[0];
    const uint64_t s0 = rs[1];
    rs[0] = s0;
    s1 ^= s1 << 23;
    rs[1] = s1 ^ s0 ^ (s1 >> 18) ^ (s0 >> 5);
    return rs[1] + s0;
}

static int rnd_int(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd_unit(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int DEG, DIAM;
static double END_T;

/* Group Z_M x|_R Z_K2; element a*K2 + b; (a,b)(c,e) = (a + R^b c, b + e). Order G = M*K2. */
static int M, K2, R, G;
static int *Rpow;
static int *RT, *RI;          /* RT[i*G+g] = g*S_i, RI[i*G+g] = g*S_i^{-1} */
static int Sv[MAXDEG], Si[MAXDEG];
static int *stamp, curst, *fr, *nx;
static int *bestE;
static int bestG = 0;

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long powmod_l(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static inline int gmul(int x, int y) {
    int a = x / K2, b = x % K2;
    int c = y / K2, e = y % K2;
    int ra = (int)(((long long)a + (long long)Rpow[b] * c) % M);
    int rb = (b + e) % K2;
    return ra * K2 + rb;
}

static inline int ginv(int x) {
    int a = x / K2, b = x % K2;
    int nb = (K2 - b) % K2;
    int na = (int)((M - ((long long)Rpow[nb] * a) % M) % M);
    return na * K2 + nb;
}

static void free_group(void) {
    free(Rpow); free(RT); free(RI); free(stamp); free(fr); free(nx);
    Rpow = NULL; RT = NULL; RI = NULL; stamp = NULL; fr = NULL; nx = NULL;
}

static void setup_group(int m, int k, int r) {
    M = m; K2 = k; R = r; G = m * k;
    Rpow = malloc(sizeof(int) * (size_t)K2);
    Rpow[0] = 1 % M;
    for (int b = 1; b < K2; b++) Rpow[b] = (int)((long long)Rpow[b - 1] * R % M);
    RT = malloc(sizeof(int) * (size_t)DEG * G);
    RI = malloc(sizeof(int) * (size_t)DEG * G);
    stamp = calloc((size_t)2 * G, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)2 * G);
    nx = malloc(sizeof(int) * (size_t)2 * G);
    curst = 0;
}

static void set_gen(int i, int s) {
    Sv[i] = s;
    Si[i] = ginv(s);
    for (int g = 0; g < G; g++) {
        RT[i * G + g] = gmul(g, s);
        RI[i * G + g] = gmul(g, Si[i]);
    }
}

static int in_set(int s, int upto) {
    for (int j = 0; j < upto; j++)
        if (Sv[j] == s) return 1;
    return 0;
}

/* Sum over the two side-identities of the number of vertices NOT within DIAM. */
static long cost_eval(void) {
    long bad = 0;
    int N2 = 2 * G;
    for (int src = 0; src < 2; src++) {
        if (curst >= INT_MAX - 4) {
            memset(stamp, 0, sizeof(int) * (size_t)N2);
            curst = 0;
        }
        curst++;
        int *f = fr, *h = nx;
        int fsz = 1, count = 1;
        int s0 = src ? G : 0;
        f[0] = s0;
        stamp[s0] = curst;
        for (int lvl = 0; lvl < DIAM && fsz > 0; lvl++) {
            int nsz = 0;
            for (int q = 0; q < fsz; q++) {
                int v = f[q];
                if (v < G) {
                    for (int i = 0; i < DEG; i++) {
                        int w = G + RT[i * G + v];
                        if (stamp[w] != curst) {
                            stamp[w] = curst;
                            h[nsz++] = w;
                        }
                    }
                } else {
                    int hv = v - G;
                    for (int i = 0; i < DEG; i++) {
                        int w = RI[i * G + hv];
                        if (stamp[w] != curst) {
                            stamp[w] = curst;
                            h[nsz++] = w;
                        }
                    }
                }
            }
            count += nsz;
            int *t = f; f = h; h = t;
            fsz = nsz;
        }
        bad += N2 - count;
    }
    return bad;
}

/* Anneal the connection set S (0 always in S). Returns final cost; 0 means valid.
 * On return with cost 0 the current Sv is the valid set. */
static long run_sa(long iters) {
    set_gen(0, 0);
    for (int i = 1; i < DEG; i++) {
        int s;
        do { s = 1 + rnd_int(G - 1); } while (in_set(s, i));
        set_gen(i, s);
    }
    long c = cost_eval();
    for (long it = 0; it < iters && c > 0; it++) {
        if ((it & 255) == 0 && now() > END_T) break;
        int i = 1 + rnd_int(DEG - 1);
        int s = 1 + rnd_int(G - 1);
        if (in_set(s, DEG)) continue;
        int old = Sv[i];
        set_gen(i, s);
        long c2 = cost_eval();
        double T = 2.0 * (1.0 - (double)it / (double)iters) + 0.05;
        if (c2 <= c || rnd_unit() < exp(-(double)(c2 - c) / T)) {
            c = c2;
        } else {
            set_gen(i, old);
        }
    }
    return c;
}

static void save_best(void) {
    free(bestE);
    bestE = malloc(sizeof(int) * 2 * (size_t)G * DEG);
    long c = 0;
    for (int g = 0; g < G; g++)
        for (int i = 0; i < DEG; i++) {
            bestE[2 * c] = g;
            bestE[2 * c + 1] = G + RT[i * G + g];
            c++;
        }
    bestG = G;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit nlo\n", argv[0]);
        return 2;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    double limit = atof(argv[4]);
    long nlo = atol(argv[5]);
    if (DEG < 2 || DEG > MAXDEG || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    END_T = now() + limit;
    uint64_t sm = sd * 2654435761ULL + 99991ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    /* Half of the Moore bound: sum_{i<DIAM} (DEG-1)^i. */
    long maxG = 0, pw = 1;
    for (int i = 0; i < DIAM; i++) {
        maxG += pw;
        pw *= (DEG - 1);
        if (maxG > 1000000L) break;
    }

    if (nlo < DEG) nlo = DEG;
    long NLO = nlo;
    while (now() < END_T && NLO <= maxG) {
        long W = 60;
        if (NLO + W - 1 > maxG) W = maxG - NLO + 1;
        double u = rnd_unit();
        long n = NLO + (long)((double)W * u * u);
        if (n > maxG) n = maxG;
        if (n < DEG) continue;

        int divs[512];
        int nd = 0;
        for (long dv = 1; dv <= n && nd < 512; dv++)
            if (n % dv == 0) divs[nd++] = (int)dv;
        int mm = divs[rnd_int(nd)];
        int kk = (int)(n / mm);
        int rr = 0;
        if (mm > 1) {
            int ok = 0;
            int st = 1 + rnd_int(mm - 1);
            for (int tt = 0; tt < mm - 1 && !ok; tt++) {
                int c = 1 + (st - 1 + tt) % (mm - 1);
                if (gcd_i(c, mm) == 1 && powmod_l(c, kk, mm) == 1 % mm) {
                    rr = c;
                    ok = 1;
                }
            }
            if (!ok) continue;
        }

        setup_group(mm, kk, rr);
        long iters = 4000 + rnd_int(4001);
        long c = run_sa(iters);
        if (c == 0) {
            save_best();
            NLO = n + 1;
        }
        free_group();
    }

    if (bestG <= 0) {
        printf("0 0\n");
        return 0;
    }
    long mE = (long)bestG * DEG;
    printf("%d %ld\n", 2 * bestG, mE);
    for (long e = 0; e < mE; e++)
        printf("%d %d\n", bestE[2 * e], bestE[2 * e + 1]);
    return 0;
}
"""


def _known_start(d, D):
    """Known Python constructions for D = 3, or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    start = _known_start(d, D)
    if start is not None and not lib.is_valid(start[0], start[1], d, D):
        start = None
    best = start if start is not None else lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))

    moore = lib.moore_bound(d, D)
    if best[0] >= moore or d < 2:
        return best

    budget = 0.75 * time_limit - (time.monotonic() - t0) - 2.0
    if budget < 2.0:
        return best

    # Sweep Cayley-bipartite orders from a low start; the C engine climbs on success.
    nlo = max(best[0] // 2 + 1, d, int(0.3 * (moore // 2)))
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", nlo],
                         timeout=budget + 8.0)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass   # keep the valid fallback

    return best
