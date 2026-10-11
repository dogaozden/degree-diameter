import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine v2: voltage lifts over a wider family of finite groups.
#
# Groups (order n, built inside C as multiplication tables):
#   type 0: Z_m^r semidirect Z_k, (v,b)(w,e) = (v + M^b w, b+e), with M^k = I mod m.
#           r = 1 gives the metacyclic groups of the previous engine. r = 2, 3 gives
#           non-cyclic groups, including elementary abelian ones when M = I.
#   type 1: Heisenberg group H(m) x Z_k, (a,b,c,z)(a',b',c',z') = (a+a', b+b', c+c'+a b', z+z').
#           This is non-metacyclic, so it is outside the old search space.
#
# Base: K A-vertices and K B-vertices. Each of DEG layers is a permutation i -> j,
# with dart (i, j, s) joining A_{i,g} to B_{j, g*s} for all g. Left multiplication
# is an automorphism, so diameter <= D iff a BFS of depth D from each of the 2K block
# representatives covers the whole graph.
#
# Search: simulated annealing on a breakout-weighted cost (weights raised on blocks
# that stay uncovered), plus an elite pool with iterated local search. Groups are
# drawn from candidates with order in a window just above the current record.
# Half of the fresh groups are cyclic-by-cyclic (type 0, r = 1), which keeps the
# proven search space in play.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define BIGC 1000000000LL
#define KMAX 4
#define MAXDEG 16
#define MAXT (MAXDEG * KMAX)
#define NMAX 1300
#define ITERS 6000
#define ILS_ITERS 3000
#define POOLMAX 48
#define POOLP 0.6
#define BRK 150
#define CANDMAX 8192

typedef struct {
    int type;          /* 0: Z_m^r (+) Z_k with matrix action; 1: Heisenberg(m) x Z_k */
    int r, m, k, n;
    int M[3][3];
    int Mp[12][3][3];  /* Mp[b] = M^b mod m for b < k (type 0) */
} Grp;

typedef struct {
    Grp g;
    int K;
    long long cost;
    int J[MAXT];
    int S[MAXT];
} Cfg;

static uint64_t rs[2];
static struct timespec T0;
static double DEADLINE = 0.0;

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

static int DEG, DIAM;
static int K, T, n, N;
static Grp cur;
static int MT[NMAX * NMAX];
static int dI[MAXT], dJ[MAXT], dS[MAXT], bestJ[MAXT], bestS[MAXT];
static int perm[MAXT * NMAX];
static int adj[2 * KMAX * NMAX * MAXDEG];
static int cnt[2 * KMAX * NMAX], stamp[2 * KMAX * NMAX], fr[2 * KMAX * NMAX], nx[2 * KMAX * NMAX];
static int curstamp = 0;
static long long wt[2 * KMAX], unc[2 * KMAX];
static long long wsum_w = 0, last_w = 0;
static int best_n = 0, best_m = 0;
static int best_e[2 * MAXT * NMAX];
static Cfg pool[POOLMAX];
static int npool = 0;

static int dvec[NMAX][3];
static int dblk[NMAX];
static int d1a[NMAX], d1b[NMAX], d1c[NMAX], d1z[NMAX];

static void mat_mul(int r, int m, int A[3][3], int B[3][3], int C[3][3]) {
    int R[3][3] = {{0, 0, 0}, {0, 0, 0}, {0, 0, 0}};
    for (int i = 0; i < r; i++)
        for (int j = 0; j < r; j++) {
            long long s = 0;
            for (int l = 0; l < r; l++) s += (long long)A[i][l] * B[l][j];
            R[i][j] = (int)(s % m);
        }
    memcpy(C, R, sizeof(R));
}

static void mat_id(int r, int m, int A[3][3]) {
    memset(A, 0, sizeof(int) * 9);
    for (int i = 0; i < r; i++) A[i][i] = 1 % m;
}

/* Multiplication table of g: MT[x*n+y] = x*y, elements coded as described above. */
static void build_table(const Grp *g) {
    int nn = g->n;
    int m = g->m;
    int k = g->k;
    if (g->type == 0) {
        int r = g->r;
        long long mr = 1;
        for (int i = 0; i < r; i++) mr *= m;
        for (int y = 0; y < nn; y++) {
            long long t = y % mr;
            dblk[y] = (int)(y / mr);
            for (int i = 0; i < r; i++) {
                dvec[y][i] = (int)(t % m);
                t /= m;
            }
        }
        for (int x = 0; x < nn; x++) {
            long long t = x % mr;
            int bx = (int)(x / mr);
            int vx[3] = {0, 0, 0};
            for (int i = 0; i < r; i++) {
                vx[i] = (int)(t % m);
                t /= m;
            }
            for (int y = 0; y < nn; y++) {
                int nb = (bx + dblk[y]) % k;
                long long idx = 0, pw = 1;
                for (int i = 0; i < r; i++) {
                    long long s = vx[i];
                    for (int j = 0; j < r; j++)
                        s += (long long)g->Mp[bx][i][j] * dvec[y][j];
                    idx += (s % m) * pw;
                    pw *= m;
                }
                MT[x * nn + y] = (int)(nb * mr + idx);
            }
        }
    } else {
        long long m2 = (long long)m * m;
        long long m3 = m2 * m;
        for (int y = 0; y < nn; y++) {
            long long rem = y % m3;
            d1z[y] = (int)(y / m3);
            d1a[y] = (int)(rem / m2);
            d1b[y] = (int)((rem / m) % m);
            d1c[y] = (int)(rem % m);
        }
        for (int x = 0; x < nn; x++) {
            long long rem = x % m3;
            int zx = (int)(x / m3);
            int ax = (int)(rem / m2);
            int bx = (int)((rem / m) % m);
            int cx = (int)(rem % m);
            for (int y = 0; y < nn; y++) {
                int na = (ax + d1a[y]) % m;
                int nb = (bx + d1b[y]) % m;
                int nc = (int)((cx + d1c[y] + (long long)ax * d1b[y]) % m);
                int nz = (zx + d1z[y]) % k;
                MT[x * nn + y] = (int)(nz * m3 + na * m2 + nb * m + nc);
            }
        }
    }
}

/* Type 0 group Z_m^r semidirect Z_k. Trial 0 is M = I, which always passes. */
static void make_type0(Grp *g, int r, int m, int k) {
    g->type = 0;
    g->r = r;
    g->m = m;
    g->k = k;
    long long mr = 1;
    for (int i = 0; i < r; i++) mr *= m;
    g->n = (int)(mr * k);
    int M[3][3], P[3][3], Q[3][3];
    for (int trial = 0; trial < 300; trial++) {
        memset(M, 0, sizeof(M));
        if (trial == 0) {
            mat_id(r, m, M);
        } else if (trial % 3 == 1) {
            int p[3] = {0, 1, 2};
            for (int i = r - 1; i > 0; i--) {
                int j = rnd_int(i + 1);
                int tmp = p[i]; p[i] = p[j]; p[j] = tmp;
            }
            for (int i = 0; i < r; i++) M[i][p[i]] = (rnd_int(2) ? 1 : m - 1);
        } else if (trial % 3 == 2) {
            for (int i = 0; i < r; i++)
                for (int j = 0; j < r; j++) {
                    int v = rnd_int(3);
                    M[i][j] = (v == 0) ? 0 : (v == 1 ? 1 : m - 1);
                }
        } else {
            for (int i = 0; i < r; i++)
                for (int j = 0; j < r; j++) M[i][j] = rnd_int(m);
        }
        mat_id(r, m, P);
        for (int b = 0; b < k; b++) {
            memcpy(g->Mp[b], P, sizeof(P));
            mat_mul(r, m, P, M, Q);
            memcpy(P, Q, sizeof(P));
        }
        int ok = 1;
        for (int i = 0; i < r; i++)
            for (int j = 0; j < r; j++)
                if (P[i][j] != ((i == j) ? 1 % m : 0)) ok = 0;
        if (ok) {
            memcpy(g->M, M, sizeof(M));
            return;
        }
    }
}

/* Random group whose order lies in [lo, hi]. If only_r1, first try cyclic-by-cyclic groups. */
static void choose_group(int lo, int hi, int only_r1, Grp *out) {
    static int cr[CANDMAX], cm[CANDMAX], ck[CANDMAX], ct[CANDMAX];
    int nc = 0;
    for (int pass = 0; pass < 2; pass++) {
        int r1only = (pass == 0) && only_r1;
        nc = 0;
        for (int r = 1; r <= 3; r++) {
            if (r1only && r != 1) continue;
            for (int k = 1; k <= 12; k++) {
                for (int m = 2;; m++) {
                    long long p = 1;
                    for (int i = 0; i < r; i++) p *= m;
                    long long nn = p * k;
                    if (nn > hi) break;
                    if (nn >= lo && nc < CANDMAX) {
                        ct[nc] = 0; cr[nc] = r; cm[nc] = m; ck[nc] = k; nc++;
                    }
                }
            }
        }
        if (!r1only) {
            for (int k = 1; k <= 12; k++) {
                for (int m = 2;; m++) {
                    long long nn = (long long)m * m * m * k;
                    if (nn > hi) break;
                    if (nn >= lo && nc < CANDMAX) {
                        ct[nc] = 1; cr[nc] = 0; cm[nc] = m; ck[nc] = k; nc++;
                    }
                }
            }
        }
        if (nc > 0) break;
    }
    if (nc == 0) {
        make_type0(out, 1, lo, 1);
        return;
    }
    int c = rnd_int(nc);
    if (ct[c] == 0) {
        make_type0(out, cr[c], cm[c], ck[c]);
    } else {
        out->type = 1;
        out->r = 0;
        out->m = cm[c];
        out->k = ck[c];
        out->n = cm[c] * cm[c] * cm[c] * ck[c];
        mat_id(0, cm[c], out->M);
    }
}

static void build_perm(int t) {
    int s = dS[t];
    int *pm = perm + (size_t)t * n;
    for (int g = 0; g < n; g++) pm[g] = MT[g * n + s];
}

static void setup_group(int K_, const Grp *g) {
    K = K_;
    cur = *g;
    n = g->n;
    T = DEG * K;
    N = 2 * K * n;
    build_table(&cur);
    for (int t = 0; t < T; t++) dI[t] = t % K;
    for (int b = 0; b < 2 * K; b++) {
        wt[b] = 1;
        unc[b] = 0;
    }
    wsum_w = 2 * K;
}

/* Returns the true cost (sum of uncovered ordered pairs over block reps). Sets unc[r], last_w. */
static long long eval_cost(void) {
    for (int t1 = 0; t1 < T; t1++)
        for (int t2 = t1 + 1; t2 < T; t2++)
            if (dI[t1] == dI[t2] && dJ[t1] == dJ[t2] && dS[t1] == dS[t2]) {
                for (int r = 0; r < 2 * K; r++) unc[r] = 0;
                last_w = BIGC;
                return BIGC;
            }
    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int t = 0; t < T; t++) {
        int ai = dI[t] * n, bj = (K + dJ[t]) * n;
        const int *pm = perm + (size_t)t * n;
        for (int g = 0; g < n; g++) {
            int a = ai + g, b = bj + pm[g];
            adj[(size_t)a * DEG + cnt[a]++] = b;
            adj[(size_t)b * DEG + cnt[b]++] = a;
        }
    }
    long long total = 0;
    for (int r = 0; r < 2 * K; r++) {
        int src = r * n;
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
        unc[r] = N - count;
        total += N - count;
    }
    long long w = 0;
    for (int r = 0; r < 2 * K; r++) w += wt[r] * unc[r];
    last_w = w;
    return total;
}

static void random_init(void) {
    int p[KMAX];
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
            dS[t] = rnd_int(n);
        }
    }
    for (int t = 0; t < T; t++) build_perm(t);
}

/* Random kicks: target swaps within a layer, and element changes. Both keep layers permutations. */
static void perturb(int nmoves) {
    for (int s = 0; s < nmoves; s++) {
        if (K > 1 && rnd_unit() < 0.3) {
            int l = rnd_int(DEG);
            int i1 = rnd_int(K), i2 = rnd_int(K);
            if (i1 == i2) continue;
            int t1 = l * K + i1, t2 = l * K + i2;
            int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
        } else {
            int t = rnd_int(T);
            dS[t] = rnd_int(n);
            build_perm(t);
        }
    }
}

/* Annealing on the breakout-weighted cost. Caller must have just called eval_cost(). */
static long long run_sa(int iters, double tscale, long long cost) {
    long long bestc = cost;
    long long wcur = last_w;
    long long prevc = cost;
    memcpy(bestJ, dJ, sizeof(int) * (size_t)T);
    memcpy(bestS, dS, sizeof(int) * (size_t)T);
    for (int it = 0; it < iters && bestc > 0; it++) {
        if ((it & 63) == 0 && elapsed() > DEADLINE) break;
        if (it > 0 && it % BRK == 0) {
            if (cost < BIGC && cost >= prevc) {
                eval_cost();
                for (int r = 0; r < 2 * K; r++)
                    if (unc[r] > 0) { wt[r]++; wsum_w++; }
                wcur = 0;
                for (int r = 0; r < 2 * K; r++) wcur += wt[r] * unc[r];
            }
            prevc = cost;
        }
        double sc = (double)wsum_w / (2.0 * K);
        double temp = tscale * (3.0 * (1.0 - (double)it / iters) + 0.05) * sc;
        if (K > 1 && rnd_unit() < 0.25) {
            int l = rnd_int(DEG);
            int i1 = rnd_int(K), i2 = rnd_int(K);
            if (i1 == i2) continue;
            int t1 = l * K + i1, t2 = l * K + i2;
            int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
            long long c2 = eval_cost();
            long long w2 = last_w;
            if (w2 <= wcur || rnd_unit() < exp(-(double)(w2 - wcur) / temp)) {
                cost = c2;
                wcur = w2;
            } else {
                tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
            }
        } else {
            int t = rnd_int(T);
            int olds = dS[t];
            int news = rnd_int(n);
            if (news == olds) continue;
            dS[t] = news;
            build_perm(t);
            long long c2 = eval_cost();
            long long w2 = last_w;
            if (w2 <= wcur || rnd_unit() < exp(-(double)(w2 - wcur) / temp)) {
                cost = c2;
                wcur = w2;
            } else {
                dS[t] = olds;
                build_perm(t);
            }
        }
        if (cost < bestc) {
            bestc = cost;
            memcpy(bestJ, dJ, sizeof(int) * (size_t)T);
            memcpy(bestS, dS, sizeof(int) * (size_t)T);
        }
    }
    return bestc;
}

static void emit(void) {
    int idx = 0;
    for (int t = 0; t < T; t++) {
        for (int g = 0; g < n; g++) {
            best_e[idx++] = dI[t] * n + g;
            best_e[idx++] = (K + dJ[t]) * n + perm[(size_t)t * n + g];
        }
    }
    best_m = T * n;
    best_n = 2 * K * n;
}

/* A zero-cost run is a valid graph: load it and emit if it beats the best so far. */
static void finish_run(long long bc) {
    if (bc == 0) {
        memcpy(dJ, bestJ, sizeof(int) * (size_t)T);
        memcpy(dS, bestS, sizeof(int) * (size_t)T);
        for (int t = 0; t < T; t++) build_perm(t);
        if (2 * K * n > best_n) emit();
    }
}

static void pool_add(long long cost, const int *J, const int *S) {
    if (cost <= 0 || cost >= BIGC) return;
    int slot;
    if (npool < POOLMAX) {
        slot = npool++;
    } else {
        slot = 0;
        for (int i = 1; i < POOLMAX; i++)
            if (pool[i].cost > pool[slot].cost) slot = i;
        if (pool[slot].cost <= cost) return;
    }
    Cfg *c = &pool[slot];
    c->g = cur;
    c->K = K;
    c->cost = cost;
    memcpy(c->J, J, sizeof(int) * (size_t)T);
    memcpy(c->S, S, sizeof(int) * (size_t)T);
}

/* Pool entries whose group order still beats the best; best of 3 samples by cost. */
static int pick_pool(void) {
    int cand[POOLMAX], nc = 0;
    for (int i = 0; i < npool; i++) {
        long long nn = 2LL * pool[i].K * pool[i].g.n;
        if (nn > best_n) cand[nc++] = i;
    }
    if (nc == 0) return -1;
    int bi = cand[rnd_int(nc)];
    for (int s = 0; s < 2; s++) {
        int c = cand[rnd_int(nc)];
        if (pool[c].cost < pool[bi].cost) bi = c;
    }
    return bi;
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
    if (DEG < 1 || DIAM < 1 || DEG > MAXDEG) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    static const int kch[8] = {1, 1, 2, 2, 2, 3, 3, 4};
    while (elapsed() < DEADLINE) {
        int pi = -1;
        if (rnd_unit() < POOLP) pi = pick_pool();
        if (pi >= 0) {
            /* Iterated local search: perturb an elite configuration and re-anneal. */
            Cfg c = pool[pi];
            setup_group(c.K, &c.g);
            memcpy(dJ, c.J, sizeof(int) * (size_t)T);
            memcpy(dS, c.S, sizeof(int) * (size_t)T);
            for (int t = 0; t < T; t++) build_perm(t);
            perturb(2 + rnd_int(4));
            for (int t = 0; t < T; t++) build_perm(t);
            long long cst = eval_cost();
            long long bc = run_sa(ILS_ITERS, 0.35, cst);
            finish_run(bc);
            pool_add(bc, bestJ, bestS);
            continue;
        }

        /* Fresh random lift over a group of order just above the record divided by 2K. */
        int Kc = kch[rnd_int(8)];
        int lo = best_n / (2 * Kc) + 1;
        if (lo < 2) lo = 2;
        int hi = lo + lo / 5 + 3;
        if (hi > NMAX) hi = NMAX;
        if (lo > hi) continue;
        Grp g;
        choose_group(lo, hi, rnd_unit() < 0.5, &g);
        setup_group(Kc, &g);
        random_init();
        long long cost = eval_cost();
        long long bc = run_sa(ITERS, 1.0, cost);
        finish_run(bc);
        pool_add(bc, bestJ, bestS);
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
# Safe baseline families (valid fallbacks, always checked with lib.is_valid).
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


# ----------------------------------------------------------------------------
# Driver: baselines in Python, then the C group-lift search over the wider family.
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

    if D >= 4 and time.monotonic() - start < 0.3 * time_limit:
        try:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])
        except Exception:
            pass

    # Already at the Moore bound: nothing larger is possible.
    if best_n >= lib.moore_bound(d, D):
        return best

    # Give the C search nearly all of the budget. Its deadline counts from process
    # start, so leave room for parsing and validation.
    elapsed = time.monotonic() - start
    remaining = 0.9 * time_limit - elapsed - 1.0
    if remaining >= 1.0:
        hard = min(remaining + 3.0, time_limit - elapsed - 1.5)
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
