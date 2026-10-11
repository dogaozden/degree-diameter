import time

import lib


# ----------------------------------------------------------------------------
# Approach: bi-Cayley lifts searched by tabu search, not annealing.
#
# A candidate has K A-blocks and K B-blocks over a group H = Z_m x|_r Z_c2 of
# order G. Layer l (0 <= l < DEG) is a permutation p_l of the K block indices,
# so dart (i, p_l(i), s) joins A_i,g to B_{p_l(i)}, g*s for all g in H. Every
# vertex then has degree DEG. Left multiplication by H is an automorphism, so
# the diameter is <= DIAM iff a BFS of depth DIAM from the identity of each of
# the 2K blocks reaches everything.
#
# Search: each step samples a batch of random moves (change one voltage, or
# swap two targets inside one layer), takes the best non-tabu move (aspiration
# when it beats the group's best), and keeps a tabu tenure on the touched darts.
# A group is abandoned after NOIMP steps without improvement. The group order
# is chosen so that 2KG is strictly above the current best order, so every hit
# is a new record for this run. Several block counts K are tried.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define BIGC 1000000000LL
#define NSAMP 24
#define NOIMP 2500
#define MAXKB 8

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

static double elapsed(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)(ts.tv_sec - T0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - T0.tv_nsec);
}

static int DEG, DIAM, K, K2, M, R, G, T, N;
static int *Rpow, *dI, *dJ, *dS, *perm, *adj, *cnt, *stamp, *fr, *nx, *tabu;
static int curstamp;
static int best_n = 0, best_m = 0;
static int *best_e = NULL;

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

/* (a,b)*(c,e) = (a + r^b c, b + e); element index a*K2 + b, identity = 0. */
static int gmul(int x, int y) {
    int a = x / K2, b = x % K2;
    int c = y / K2, e = y % K2;
    int ra = (int)(((long long)a + (long long)Rpow[b] * c) % M);
    int rb = (b + e) % K2;
    return ra * K2 + rb;
}

static void build_perm(int t) {
    int s = dS[t];
    int *pm = perm + (size_t)t * G;
    for (int g = 0; g < G; g++) pm[g] = gmul(g, s);
}

static void setup(int k, int c2, int m, int r) {
    K = k; K2 = c2; M = m; R = r;
    G = m * c2;
    T = DEG * K;
    N = 2 * K * G;
    dI = malloc(sizeof(int) * (size_t)T);
    dJ = malloc(sizeof(int) * (size_t)T);
    dS = malloc(sizeof(int) * (size_t)T);
    tabu = calloc((size_t)T, sizeof(int));
    perm = malloc(sizeof(int) * (size_t)T * G);
    adj = malloc(sizeof(int) * (size_t)N * DEG);
    cnt = malloc(sizeof(int) * (size_t)N);
    stamp = calloc((size_t)N, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)N);
    nx = malloc(sizeof(int) * (size_t)N);
    Rpow = malloc(sizeof(int) * (size_t)K2);
    Rpow[0] = 1 % M;
    for (int b = 1; b < K2; b++) Rpow[b] = (int)((long long)Rpow[b - 1] * R % M);
    curstamp = 0;
    for (int t = 0; t < T; t++) dI[t] = t % K;
}

static void teardown(void) {
    free(dI); free(dJ); free(dS); free(tabu); free(perm);
    free(adj); free(cnt); free(stamp); free(fr); free(nx); free(Rpow);
    dI = dJ = dS = perm = adj = cnt = stamp = fr = nx = Rpow = NULL;
    tabu = NULL;
}

/* True cost: uncovered ordered pairs summed over the 2K block identities.
   Zero iff the lift has diameter <= DIAM. Duplicate darts get a penalty. */
static long long eval_cost(void) {
    int dups = 0;
    for (int t1 = 0; t1 < T; t1++)
        for (int t2 = t1 + 1; t2 < T; t2++)
            if (dI[t1] == dI[t2] && dJ[t1] == dJ[t2] && dS[t1] == dS[t2]) dups++;
    if (dups) return BIGC + dups;

    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int t = 0; t < T; t++) {
        int ai = dI[t] * G, bj = (K + dJ[t]) * G;
        const int *pm = perm + (size_t)t * G;
        for (int g = 0; g < G; g++) {
            int a = ai + g, b = bj + pm[g];
            adj[(size_t)a * DEG + cnt[a]++] = b;
            adj[(size_t)b * DEG + cnt[b]++] = a;
        }
    }

    long long total = 0;
    for (int r = 0; r < 2 * K; r++) {
        int src = r * G;
        if (curstamp >= 2000000000) {
            memset(stamp, 0, sizeof(int) * (size_t)N);
            curstamp = 0;
        }
        curstamp++;
        int *f = fr, *h = nx;
        int fsz = 1, count = 1;
        f[0] = src;
        stamp[src] = curstamp;
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
        total += N - count;
    }
    return total;
}

static void random_init(void) {
    int p[MAXKB];
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
    for (int t = 0; t < T; t++) build_perm(t);
}

static void emit(void) {
    int m = T * G;
    free(best_e);
    best_e = malloc(sizeof(int) * 2 * (size_t)m);
    int idx = 0;
    for (int t = 0; t < T; t++) {
        for (int g = 0; g < G; g++) {
            best_e[idx++] = dI[t] * G + g;
            best_e[idx++] = (K + dJ[t]) * G + perm[(size_t)t * G + g];
        }
    }
    best_m = m;
    best_n = N;
}

/* Tabu search on the current group. Returns 1 if a zero-cost lift was reached
   (the state is then left in place), 0 on stagnation or deadline. */
static int tabu_search(void) {
    long long cur = eval_cost();
    long long bestc = cur;
    int noimp = 0, it = 0;
    for (int i = 0; i < T; i++) tabu[i] = 0;
    while (1) {
        if (cur == 0) return 1;
        if (noimp >= NOIMP) return 0;
        if (elapsed() > DEADLINE) return 0;
        it++;
        long long bc = 4 * BIGC;
        int bty = -1, bt1 = -1, bt2 = -1, bnv = -1;
        for (int s = 0; s < NSAMP; s++) {
            if (K > 1 && rnd_int(4) == 0) {
                int l = rnd_int(DEG);
                int i1 = rnd_int(K), i2 = rnd_int(K);
                if (i1 == i2) continue;
                int t1 = l * K + i1, t2 = l * K + i2;
                int hit = (tabu[t1] > it || tabu[t2] > it);
                int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
                long long c = eval_cost();
                tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
                if (hit && !(c < bestc)) continue;
                if (c < bc) { bc = c; bty = 1; bt1 = t1; bt2 = t2; }
            } else {
                int t = rnd_int(T);
                int nv = rnd_int(G);
                if (nv == dS[t]) continue;
                int olds = dS[t];
                int hit = (tabu[t] > it);
                dS[t] = nv; build_perm(t);
                long long c = eval_cost();
                dS[t] = olds; build_perm(t);
                if (hit && !(c < bestc)) continue;
                if (c < bc) { bc = c; bty = 0; bt1 = t; bnv = nv; }
            }
        }
        if (bty < 0) { noimp++; continue; }
        if (bty == 1) {
            int tmp = dJ[bt1]; dJ[bt1] = dJ[bt2]; dJ[bt2] = tmp;
            int ten = 2 + rnd_int(T + 2);
            tabu[bt1] = it + ten;
            tabu[bt2] = it + ten;
        } else {
            dS[bt1] = bnv;
            build_perm(bt1);
            tabu[bt1] = it + 2 + rnd_int(T + 2);
        }
        cur = bc;
        if (cur < bestc) { bestc = cur; noimp = 0; }
        else noimp++;
    }
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
    if (DEG < 1 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    static const int kch[8] = {1, 2, 2, 3, 3, 4, 5, 6};
    while (elapsed() < DEADLINE) {
        int k = kch[rnd_int(8)];
        int gmin = best_n / (2 * k) + 1;
        if (gmin < 2) gmin = 2;
        int g = gmin + rnd_int(gmin / 8 + 3);

        int opts[16], no = 0;
        for (int c = 1; c <= 12; c++)
            if (g % c == 0 && g / c >= 2) opts[no++] = c;
        if (no == 0) continue;
        int c2 = opts[rnd_int(no)];
        int m = g / c2, r = 1;
        if (c2 > 1) {
            for (int tr = 0; tr < 200; tr++) {
                int cand = 1 + rnd_int(m - 1);
                if (gcd_i(cand, m) == 1 && powmod(cand, c2, m) == 1 % m) {
                    r = cand;
                    break;
                }
            }
        }

        setup(k, c2, m, r);
        random_init();
        int found = tabu_search();
        if (found && N > best_n) emit();
        teardown();
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
# Safe baselines, always valid.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
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

    # K_{d,d} has diameter 2, so it is valid whenever D >= 2.
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

    if best_n >= lib.moore_bound(d, D):
        return best

    # Leave room for the one-off C compile (outside the C deadline),
    # parsing and validation.
    remaining = 0.88 * time_limit - (time.monotonic() - start) - 2.0
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
