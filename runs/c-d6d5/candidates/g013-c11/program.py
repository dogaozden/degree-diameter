import time

import lib


# ----------------------------------------------------------------------------
# C engine: voltage lifts over semidirect products Z_m x| Z_k2 with K <= 2
# base vertices per side, searched by sampled tabu search.
#
# Each step samples NS random neighbours (change one dart's group element, or
# swap two targets inside a layer), evaluates each by BFS from the 2K block
# representatives, applies the best non-tabu one (aspiration allows a tabu
# move that beats the run's best), and keeps the best state by true cost.
# Breakout weights on blocks still uncovered are bumped when the weighted cost
# stagnates. Zero true cost means a valid graph.
#
# Vertices: A_i,g = i*G + g and B_j,h = (K+j)*G + h. Dart t = (Ai[t], Bj[t], S[t])
# joins A_i,g to B_j,g*S[t] for all g. Each layer's targets form a permutation,
# so every vertex has degree DEG. Left multiplication is an automorphism, so
# diameter <= DIAM iff BFS of depth DIAM from each block representative covers all.
# The deadline uses wall-clock time from program start.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define BIGC 1000000000LL
#define ITERS 2500
#define NS 60
#define TT 7
#define STAG 40
#define MAXDEG 12
#define MAXK 2

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

static int powmod(long long b, int e, int m) {
    long long r = 1 % m, x = b % m;
    while (e) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

static int DEG, DIAM, K, K2, M, G, T, N, R;
static int *Rpow, *Ai, *Bj, *S, *perm, *adj, *cnt, *stamp, *fr, *nx;
static int *tabu_until, *bBj, *bS, *best_e;
static int curstamp;
static long long *wt, *unc, last_w;
static int best_n = 0, best_m = 0;

/* (a,b)*(c,e) = (a + r^b c, b + e), element index a*K2 + b. */
static int gmul(int x, int y) {
    int a = x / K2, b = x - a * K2;
    int c = y / K2, e = y - c * K2;
    int ra = (int)(((long long)a + (long long)Rpow[b] * c) % M);
    int rb = (b + e) % K2;
    return ra * K2 + rb;
}

static void build_perm(int t) {
    int s = S[t];
    int *pm = perm + (size_t)t * G;
    for (int g = 0; g < G; g++) pm[g] = gmul(g, s);
}

static void alloc_group(int k, int c2, int m, int r) {
    K = k; K2 = c2; M = m; R = r;
    G = m * c2;
    N = 2 * K * G;
    T = DEG * K;
    Ai = malloc(sizeof(int) * (size_t)T);
    Bj = malloc(sizeof(int) * (size_t)T);
    S = malloc(sizeof(int) * (size_t)T);
    bBj = malloc(sizeof(int) * (size_t)T);
    bS = malloc(sizeof(int) * (size_t)T);
    tabu_until = calloc((size_t)T, sizeof(int));
    perm = malloc(sizeof(int) * (size_t)T * G);
    adj = malloc(sizeof(int) * (size_t)N * DEG);
    cnt = malloc(sizeof(int) * (size_t)N);
    stamp = calloc((size_t)N, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)N);
    nx = malloc(sizeof(int) * (size_t)N);
    Rpow = malloc(sizeof(int) * (size_t)K2);
    wt = malloc(sizeof(long long) * (size_t)(2 * K));
    unc = malloc(sizeof(long long) * (size_t)(2 * K));
    for (int b = 0; b < 2 * K; b++) { wt[b] = 1; unc[b] = 0; }
    curstamp = 0;
    Rpow[0] = 1 % M;
    for (int b = 1; b < K2; b++) Rpow[b] = (int)((long long)Rpow[b - 1] * R % M);
    for (int t = 0; t < T; t++) { Ai[t] = t % K; Bj[t] = 0; S[t] = 0; }
}

static void free_group(void) {
    free(Ai); free(Bj); free(S); free(bBj); free(bS); free(tabu_until);
    free(perm); free(adj); free(cnt); free(stamp); free(fr); free(nx); free(Rpow);
    free(wt); free(unc);
    Ai = Bj = S = bBj = bS = tabu_until = perm = adj = cnt = stamp = fr = nx = Rpow = NULL;
    wt = unc = NULL;
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
            Ai[t] = i;
            Bj[t] = p[i];
            S[t] = rnd_int(G);
        }
    }
    for (int t = 0; t < T; t++) build_perm(t);
}

static void build_adj(void) {
    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int t = 0; t < T; t++) {
        int ai = Ai[t] * G, bj = (K + Bj[t]) * G;
        const int *pm = perm + (size_t)t * G;
        for (int g = 0; g < G; g++) {
            int a = ai + g, b = bj + pm[g];
            adj[(size_t)a * DEG + cnt[a]++] = b;
            adj[(size_t)b * DEG + cnt[b]++] = a;
        }
    }
}

/* Returns the true cost (sum of uncovered vertices over block representatives).
   Sets unc[r] per block and last_w to the weighted cost. */
static long long eval(void) {
    for (int t1 = 0; t1 < T; t1++)
        for (int t2 = t1 + 1; t2 < T; t2++)
            if (Ai[t1] == Ai[t2] && Bj[t1] == Bj[t2] && S[t1] == S[t2]) {
                for (int r = 0; r < 2 * K; r++) unc[r] = N;
                last_w = BIGC;
                return BIGC;
            }
    build_adj();
    long long total = 0, w = 0;
    for (int r = 0; r < 2 * K; r++) {
        if (curstamp >= 2000000000) {
            memset(stamp, 0, sizeof(int) * (size_t)N);
            curstamp = 0;
        }
        curstamp++;
        int *f = fr, *h = nx;
        int fsz = 1, count = 1;
        f[0] = r * G;
        stamp[r * G] = curstamp;
        for (int lvl = 0; lvl < DIAM && fsz > 0; lvl++) {
            int nsz = 0;
            for (int q = 0; q < fsz; q++) {
                const int *au = adj + (size_t)f[q] * DEG;
                for (int e = 0; e < DEG; e++) {
                    int v = au[e];
                    if (stamp[v] != curstamp) {
                        stamp[v] = curstamp;
                        h[nsz++] = v;
                    }
                }
            }
            count += nsz;
            int *tmp = f; f = h; h = tmp;
            fsz = nsz;
        }
        unc[r] = N - count;
        total += unc[r];
        w += wt[r] * unc[r];
    }
    last_w = w;
    return total;
}

static void store_best(void) {
    memcpy(bBj, Bj, sizeof(int) * (size_t)T);
    memcpy(bS, S, sizeof(int) * (size_t)T);
}

/* Sampled tabu search with breakout weights. Returns the best true cost; best state in bBj/bS. */
static long long tabu_run(int iters) {
    long long cur = eval();
    long long curw = last_w;
    long long bestc = cur;
    store_best();
    for (int t = 0; t < T; t++) tabu_until[t] = 0;
    int stag = 0;
    for (int it = 0; it < iters && bestc > 0; it++) {
        if ((it & 7) == 0 && elapsed() > DEADLINE) break;
        int have = 0, mtype = 0, mt1 = 0, mt2 = 0, mval = 0;
        long long mw = 0;
        for (int s = 0; s < NS; s++) {
            int type, t1, t2 = 0, nv = 0;
            long long c2, w2;
            if (K > 1 && rnd_unit() < 0.25) {
                int l = rnd_int(DEG), i1 = rnd_int(K), i2 = rnd_int(K);
                if (i1 == i2) continue;
                t1 = l * K + i1;
                t2 = l * K + i2;
                int tmp = Bj[t1]; Bj[t1] = Bj[t2]; Bj[t2] = tmp;
                c2 = eval(); w2 = last_w;
                tmp = Bj[t1]; Bj[t1] = Bj[t2]; Bj[t2] = tmp;
                type = 1;
            } else {
                t1 = rnd_int(T);
                nv = rnd_int(G);
                if (nv == S[t1]) continue;
                int old = S[t1];
                S[t1] = nv; build_perm(t1);
                c2 = eval(); w2 = last_w;
                S[t1] = old; build_perm(t1);
                type = 0;
            }
            int tb = tabu_until[t1] > it || (type == 1 && tabu_until[t2] > it);
            if (tb && c2 >= bestc) continue;
            if (!have || w2 < mw) {
                have = 1;
                mw = w2;
                mtype = type;
                mt1 = t1;
                mt2 = t2;
                mval = nv;
            }
        }
        if (!have) continue;
        if (mtype == 1) {
            int tmp = Bj[mt1]; Bj[mt1] = Bj[mt2]; Bj[mt2] = tmp;
            tabu_until[mt2] = it + TT + rnd_int(TT);
        } else {
            S[mt1] = mval;
            build_perm(mt1);
        }
        tabu_until[mt1] = it + TT + rnd_int(TT);
        long long prevw = curw;
        cur = eval();
        curw = last_w;
        if (cur < bestc) {
            bestc = cur;
            store_best();
        }
        if (curw < prevw) stag = 0; else stag++;
        if (stag >= STAG && cur > 0) {
            for (int r = 0; r < 2 * K; r++)
                if (unc[r] > 0) wt[r]++;
            eval();
            curw = last_w;
            stag = 0;
        }
    }
    return bestc;
}

static void emit_best(void) {
    memcpy(Bj, bBj, sizeof(int) * (size_t)T);
    memcpy(S, bS, sizeof(int) * (size_t)T);
    for (int t = 0; t < T; t++) build_perm(t);
    int m = T * G;
    free(best_e);
    best_e = malloc(sizeof(int) * 2 * (size_t)m);
    int idx = 0;
    for (int t = 0; t < T; t++)
        for (int g = 0; g < G; g++) {
            best_e[idx++] = Ai[t] * G + g;
            best_e[idx++] = (K + Bj[t]) * G + perm[(size_t)t * G + g];
        }
    best_m = m;
    best_n = N;
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
    int start_n = argc > 5 ? atoi(argv[5]) : 0;
    best_n = start_n;
    best_m = 0;
    if (DEG < 1 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    while (elapsed() < DEADLINE) {
        int k = (rnd_unit() < 0.7) ? 1 : 2;
        int gmin = best_n / (2 * k) + 1;
        if (gmin < 2) gmin = 2;
        int spread = gmin / 4 + 2;
        int g = gmin + rnd_int(spread);
        int opts[MAXDEG], no = 0;
        for (int c = 1; c <= MAXDEG; c++)
            if (g % c == 0 && g / c >= 2) opts[no++] = c;
        int c2 = opts[rnd_int(no)];
        int m = g / c2, r = 1;
        if (c2 > 1 && rnd_unit() < 0.7) {
            int found = 0;
            for (int tr = 0; tr < 200 && !found; tr++) {
                int cand = 1 + rnd_int(m - 1);
                if (gcd_i(cand, m) == 1 && powmod(cand, c2, m) == 1 % m) {
                    r = cand;
                    found = 1;
                }
            }
            if (!found) {
                c2 = 1;
                m = g;
                r = 1;
            }
        }
        alloc_group(k, c2, m, r);
        random_init();
        long long bc = tabu_run(ITERS);
        if (bc == 0 && N > best_n) emit_best();
        free_group();
    }

    if (best_m > 0) {
        printf("%d %d\n", best_n, best_m);
        for (int i = 0; i < best_m; i++)
            printf("%d %d\n", best_e[2 * i], best_e[2 * i + 1]);
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


# ----------------------------------------------------------------------------
# Driver: baselines in Python, then the C tabu search.
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
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Already at the Moore bound: nothing larger is possible.
    if best_n >= lib.moore_bound(d, D):
        return best

    # Give the C search nearly all of the budget. The margin covers process
    # start, the cached compile step, parsing and validation in Python.
    remaining = 0.9 * time_limit - (time.monotonic() - start) - 1.5
    if remaining >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", best_n],
                            timeout=remaining + 8.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
