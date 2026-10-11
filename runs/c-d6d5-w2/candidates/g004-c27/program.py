import time

import lib


# ----------------------------------------------------------------------------
# Group-lift search with explicit group tables.
#
# Vertices: A_{i,x} = i*G + x and B_{j,y} = (K+j)*G + y, for x,y in the group.
# Dart t = (i, j, s) joins A_{i,x} to B_{j, x*s} for every x. Each layer l has
# one dart per A-block and one per B-block (a permutation of the K blocks), so
# every vertex has degree DEG. Left multiplication is an automorphism of the
# lift, so diameter <= D iff BFS of depth D from A_{i,e} and B_{j,e} covers
# everything (2K roots).
#
# Groups: cyclic Z_m, semidirect Z_m x| Z_k, PSL(2,p) and PGL(2,p) for small
# primes p. The non-metabelian groups PSL and PGL are the new part. The
# search climbs: each success raises the minimum group order for the next
# restart, so it always searches just above the best order found so far.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXG 2200
#define MAXDEG 16
#define MAXK 3
#define MAXV (2 * MAXK * MAXG)
#define MAXT (MAXDEG * MAXK)
#define MAXE (MAXT * MAXG)
#define ITERS 5000

static int MUL[MAXG * MAXG];
static int G, ID;

static int DEG, DIAM, K, NV, T;
static int dI[MAXT], dJ[MAXT], dS[MAXT];
static int adjv[MAXV * MAXDEG];
static int cnt[MAXV], stampv[MAXV], fr[MAXV], nxv[MAXV];
static int curstamp = 0;
static int bestE[2 * MAXE];
static int best_n = 0, best_m = 0;

static uint64_t rs[2];
static struct timespec T0;
static double DEADLINE;

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

static double elapsed(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)(ts.tv_sec - T0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - T0.tv_nsec);
}

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m, x = b % m;
    while (e) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return r;
}

/* Semidirect Z_m x| Z_k with (a,b)*(c,e) = (a + r^b c, b + e); element code a*k+b. */
static void build_semi(int m, int k, int r) {
    G = m * k;
    ID = 0;
    int pw[64];
    pw[0] = 1 % m;
    for (int b = 1; b < k; b++) pw[b] = (int)((long long)pw[b - 1] * r % m);
    for (int x = 0; x < G; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < G; y++) {
            int c = y / k, e = y % k;
            int ra = (int)(((long long)a + (long long)pw[b] * c) % m);
            MUL[x * G + y] = ra * k + (b + e) % k;
        }
    }
}

/* PSL(2,p) (pgl = 0) or PGL(2,p) (pgl = 1) as matrices mod p, canonical rep = min over scalars. */
static int PP, PGL_F;

static int canon_code(int a, int b, int c, int d) {
    int p = PP, best = -1;
    for (int lam = 1; lam < p; lam++) {
        if (!PGL_F && lam != 1 && lam != p - 1) continue;
        int code = ((((lam * a) % p) * p + (lam * b) % p) * p + (lam * c) % p) * p + (lam * d) % p;
        if (best < 0 || code < best) best = code;
    }
    return best;
}

static void build_proj(int p, int pgl) {
    PP = p;
    PGL_F = pgl;
    int P4 = p * p * p * p;
    int *idx = malloc(sizeof(int) * (size_t)P4);
    int *rep = malloc(sizeof(int) * (size_t)P4);
    for (int i = 0; i < P4; i++) idx[i] = -1;
    int nrep = 0;
    for (int code = 0; code < P4; code++) {
        int dd = code % p, cc = (code / p) % p, bb = (code / (p * p)) % p, aa = code / (p * p * p);
        int det = ((aa * dd - bb * cc) % p + p) % p;
        if (pgl ? (det == 0) : (det != 1)) continue;
        if (canon_code(aa, bb, cc, dd) != code) continue;
        idx[code] = nrep;
        rep[nrep++] = code;
    }
    G = nrep;
    for (int i = 0; i < G; i++) {
        int c1code = rep[i];
        int d1 = c1code % p, cc1 = (c1code / p) % p, b1 = (c1code / (p * p)) % p, a1 = c1code / (p * p * p);
        for (int j = 0; j < G; j++) {
            int c2code = rep[j];
            int d2 = c2code % p, cc2 = (c2code / p) % p, b2 = (c2code / (p * p)) % p, a2 = c2code / (p * p * p);
            int A = (a1 * a2 + b1 * cc2) % p;
            int B = (a1 * b2 + b1 * d2) % p;
            int C = (cc1 * a2 + d1 * cc2) % p;
            int D = (cc1 * b2 + d1 * d2) % p;
            MUL[i * G + j] = idx[canon_code(A, B, C, D)];
        }
    }
    ID = idx[canon_code(1, 0, 0, 1)];
    free(idx);
    free(rep);
}

static void random_init(void) {
    int p[MAXK];
    for (int l = 0; l < DEG; l++) {
        for (int i = 0; i < K; i++) p[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rnd_int(i + 1);
            int tmp = p[i]; p[i] = p[j]; p[j] = tmp;
        }
        for (int i = 0; i < K; i++) {
            int t = l * K + i;
            dI[t] = i;
            dJ[t] = p[i];
            dS[t] = rnd_int(G);
        }
    }
}

/* Cost = uncovered ordered pairs from the 2K block roots, plus a penalty for duplicate darts. */
static long long eval_cost(void) {
    long long dup = 0;
    for (int t1 = 0; t1 < T; t1++)
        for (int t2 = t1 + 1; t2 < T; t2++)
            if (dI[t1] == dI[t2] && dJ[t1] == dJ[t2] && dS[t1] == dS[t2]) dup++;
    memset(cnt, 0, sizeof(int) * (size_t)NV);
    for (int t = 0; t < T; t++) {
        int ai = dI[t] * G, bj = (K + dJ[t]) * G;
        for (int x = 0; x < G; x++) {
            int a = ai + x, b = bj + MUL[x * G + dS[t]];
            adjv[a * DEG + cnt[a]++] = b;
            adjv[b * DEG + cnt[b]++] = a;
        }
    }
    long long unc = 0;
    for (int r = 0; r < 2 * K; r++) {
        if (curstamp > 2000000000) {
            memset(stampv, 0, sizeof(int) * (size_t)NV);
            curstamp = 0;
        }
        curstamp++;
        int src = r * G + ID;
        int *f = fr, *h = nxv;
        int fsz = 1, count = 1;
        f[0] = src;
        stampv[src] = curstamp;
        for (int lvl = 0; lvl < DIAM && fsz > 0; lvl++) {
            int nsz = 0;
            for (int q = 0; q < fsz; q++) {
                const int *au = adjv + (size_t)f[q] * DEG;
                for (int e = 0; e < DEG; e++) {
                    int v = au[e];
                    if (stampv[v] != curstamp) {
                        stampv[v] = curstamp;
                        h[nsz++] = v;
                    }
                }
            }
            count += nsz;
            int *tmp = f; f = h; h = tmp;
            fsz = nsz;
        }
        unc += NV - count;
    }
    return unc + dup * (long long)NV;
}

static void save_best(void) {
    int idx = 0;
    for (int t = 0; t < T; t++)
        for (int x = 0; x < G; x++) {
            bestE[2 * idx] = dI[t] * G + x;
            bestE[2 * idx + 1] = (K + dJ[t]) * G + MUL[x * G + dS[t]];
            idx++;
        }
    best_m = idx;
    best_n = NV;
}

static long long anneal(int iters) {
    long long cur = eval_cost();
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 63) == 0 && elapsed() > DEADLINE) break;
        double f = (double)it / iters;
        double temp = 0.01 * NV * (1.0 - f) + 0.3;
        int type = 0, t1 = 0, t2 = 0, t = 0, olds = 0;
        if (K > 1 && rnd_unit() < 0.3) {
            int l = rnd_int(DEG), i1 = rnd_int(K), i2 = rnd_int(K);
            if (i1 == i2) continue;
            t1 = l * K + i1;
            t2 = l * K + i2;
            int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
            type = 1;
        } else {
            t = rnd_int(T);
            int news = rnd_int(G);
            olds = dS[t];
            if (news == olds) continue;
            dS[t] = news;
            type = 2;
        }
        long long c = eval_cost();
        if (c <= cur || rnd_unit() < exp(-(double)(c - cur) / temp)) {
            cur = c;
        } else if (type == 1) {
            int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
        } else {
            dS[t] = olds;
        }
    }
    if (cur == 0) save_best();
    return cur;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit [start_n]\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    best_n = argc > 5 ? atoi(argv[5]) : 0;
    best_m = 0;
    if (DEG < 1 || DEG > MAXDEG || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    static const int kopts[3] = {1, 2, 3};
    static const int kk_opts[7] = {1, 1, 2, 2, 3, 4, 6};
    static const int primes[4] = {5, 7, 11, 13};

    while (elapsed() < DEADLINE) {
        K = kopts[rnd_int(3)];
        long long lo = (best_n == 0) ? 6 : (long long)best_n / (2LL * K) + 1;
        long long hi = 2 * lo + 10;
        if (hi > MAXG) hi = MAXG;
        if (lo < 2 || lo > hi) continue;

        int built = 0;
        if (rnd_unit() < 0.35) {
            int cand[8], nc = 0;
            for (int pi = 0; pi < 4; pi++)
                for (int pg = 0; pg < 2; pg++) {
                    long long p = primes[pi];
                    long long ord = p * (p * p - 1) / (pg ? 1 : 2);
                    if (ord >= lo && ord <= hi) cand[nc++] = pi * 2 + pg;
                }
            if (nc > 0) {
                int c = cand[rnd_int(nc)];
                build_proj(primes[c / 2], c % 2);
                built = 1;
            }
        }
        if (!built) {
            int gg = (int)(lo + rnd_int((int)(hi - lo) + 1));
            int kk = kk_opts[rnd_int(7)];
            if (gg % kk != 0 || gg / kk < 2) kk = 1;
            int m = gg / kk, r = 1;
            if (kk > 1) {
                int found = 0;
                for (int tr = 0; tr < 200 && !found; tr++) {
                    int cnd = 1 + rnd_int(m - 1);
                    if (gcd_i(cnd, m) == 1 && powmod(cnd, kk, m) == 1 % m) {
                        r = cnd;
                        found = 1;
                    }
                }
                if (!found) kk = 1;
            }
            if (kk == 1) {
                m = gg;
                r = 1;
            }
            build_semi(m, kk, r);
        }

        NV = 2 * K * G;
        if (NV <= best_n || NV > MAXV) continue;
        T = DEG * K;
        random_init();
        anneal(ITERS);
    }

    if (best_m > 0) {
        printf("%d %d\n", best_n, best_m);
        for (int i = 0; i < best_m; i++)
            printf("%d %d\n", bestE[2 * i], bestE[2 * i + 1]);
    } else {
        printf("0 0\n");
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


def _araujo(d):
    """Araujo-Pardo & Lopez graph for degree d = q + 2 with q a prime power >= 3; diameter 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        return lib.araujo_lopez_graph(q)
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
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
        for builder in (_best_pg, _araujo):
            try:
                g = builder(d)
                if g is not None:
                    consider(g[0], g[1])
            except Exception:
                pass

    if d < 2 or D < 2 or best_n >= lib.moore_bound(d, D):
        return best

    # Give the C search nearly all of the budget; its deadline starts at process start.
    elapsed = time.monotonic() - start
    remaining = 0.88 * time_limit - elapsed - 1.5
    if remaining >= 1.0:
        hard = min(remaining + 3.0, time_limit - elapsed - 2.0)
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", best_n],
                            timeout=hard)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
