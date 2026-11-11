import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Engine A (bi-Cayley annealing over Z_m x| Z_k2): the parent's search, kept as
# the first stage. It gives a valid graph and a size floor for stage B.
# ----------------------------------------------------------------------------

BICAYLEY_C = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define PENALTY 1000L
#define KMAX 8

static clock_t g_t0;
static double g_budget = 1.0;
static uint64_t g_rs = 88172645463325252ULL;

/* group Z_m x| Z_k2, element a*k2+b, (a,b)(c,e) = (a + r^b c, b+e) */
static int GM = 1, GK = 1, GG = 1;
static int64_t PW[64];

static long g_best_n = 0;
static long g_best_m = 0;
static int *g_edges = NULL;

static double elapsed(void) {
    return (double)(clock() - g_t0) / (double)CLOCKS_PER_SEC;
}

static uint64_t rnext(void) {
    uint64_t x = g_rs;
    x ^= x >> 12;
    x ^= x << 25;
    x ^= x >> 27;
    g_rs = x;
    return x * 2685821657736338717ULL;
}

static uint64_t rnd(uint64_t n) {
    return n ? rnext() % n : 0;
}

static double rndf(void) {
    return (double)(rnext() >> 11) * (1.0 / 9007199254740992.0);
}

static int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    int64_t t = (a + PW[b] * (int64_t)c) % GM;
    return (int)(t * GK + (b + e) % GK);
}

static int ginv(int x) {
    int a = x / GK, b = x % GK;
    int nb = (GK - b) % GK;
    int64_t t = (-(PW[nb] * (int64_t)a)) % GM;
    if (t < 0) t += GM;
    return (int)(t * GK + nb);
}

static void set_group(int m, int k2, int64_t r) {
    GM = m;
    GK = k2;
    GG = m * k2;
    int64_t p = 1 % m;
    for (int t = 0; t < k2; t++) {
        PW[t] = p;
        p = (p * r) % m;
    }
}

static const int KCH[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};

static int64_t gcd64(int64_t a, int64_t b) {
    while (b) {
        int64_t t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static int64_t powmod(int64_t b, int64_t e, int64_t m) {
    int64_t r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int sample_group(long target, int *mo, int *ko, int64_t *ro) {
    for (int tries = 0; tries < 200; tries++) {
        int k2 = KCH[rnd(20)];
        int64_t m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        int64_t r = 1;
        if (k2 == 1) {
            r = 1;
        } else if (k2 == 2 && rndf() < 0.3) {
            r = m - 1;
            if (gcd64(r, m) != 1 || powmod(r, 2, m) != 1 % m) continue;
        } else {
            int found = 0;
            for (int t = 0; t < 60; t++) {
                int64_t c = (m > 2) ? 2 + (int64_t)rnd((uint64_t)(m - 2)) : 1;
                if (gcd64(c, m) == 1 && powmod(c, k2, m) == 1 % m) {
                    r = c;
                    found = 1;
                    break;
                }
            }
            if (!found) continue;
        }
        *mo = (int)m;
        *ko = k2;
        *ro = r;
        return 1;
    }
    return 0;
}

static int popc(uint32_t x) {
    int c = 0;
    while (x) {
        c += (int)(x & 1u);
        x >>= 1;
    }
    return c;
}

/* A-block i (vertices i*GG..) joins B-block j = lay[l][i] with voltage s = S[l][i]. */
static void set_dart(int **nbr, const int *lay, const int *S, int k, int l, int i) {
    int j = lay[l * k + i];
    int s = S[l * k + i];
    int si = ginv(s);
    int Ab = i * GG, Bb = (k + j) * GG;
    int *nb = nbr[l];
    for (int g = 0; g < GG; g++) {
        nb[Ab + g] = Bb + gmul(g, s);
        nb[Bb + g] = Ab + gmul(g, si);
    }
}

/* out[v] = bitmask of representative blocks within distance D of v. */
static void compute_reach(int **nbr, int d, int k, int N, int D, uint32_t *out, uint32_t *tmp) {
    memset(out, 0, sizeof(uint32_t) * (size_t)N);
    for (int b = 0; b < 2 * k; b++) out[b * GG] = 1u << b;
    for (int t = 0; t < D; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint32_t r = out[v];
            for (int l = 0; l < d; l++) r |= out[nbr[l][v]];
            tmp[v] = r;
            if (r != out[v]) changed = 1;
        }
        memcpy(out, tmp, sizeof(uint32_t) * (size_t)N);
        if (!changed) break;
    }
}

static long unreached(const uint32_t *reach, int k, int N) {
    long s = 0;
    for (int v = 0; v < N; v++) s += popc(reach[v]);
    return 2L * k * N - s;
}

static long dupcount(const int *lay, const int *S, int d, int k) {
    int tot = d * k;
    long dup = 0;
    for (int a = 0; a < tot; a++) {
        int la = a / k, ia = a % k;
        for (int b = 0; b < a; b++) {
            int lb = b / k, ib = b % k;
            if (ia == ib && lay[la * k + ia] == lay[lb * k + ib] && S[la * k + ia] == S[lb * k + ib]) {
                dup++;
                break;
            }
        }
    }
    return dup;
}

static void store_best(int **nbr, int d, int k) {
    long A = (long)k * GG;
    long n = 2 * A;
    if (n <= g_best_n) return;
    long cnt = A * d;
    int *e = malloc(sizeof(int) * 2 * (size_t)cnt);
    if (!e) return;
    long c = 0;
    for (long u = 0; u < A; u++) {
        for (int l = 0; l < d; l++) {
            e[2 * c] = (int)u;
            e[2 * c + 1] = nbr[l][u];
            c++;
        }
    }
    free(g_edges);
    g_edges = e;
    g_best_m = cnt;
    g_best_n = n;
}

static int run_trial(int d, int D, int k, int iters, int patience) {
    int N = 2 * k * GG;
    uint32_t full = (1u << (2 * k)) - 1u;
    int K = d * k;
    int *lay = malloc(sizeof(int) * (size_t)K);
    int *S = malloc(sizeof(int) * (size_t)K);
    int **nbr = malloc(sizeof(int *) * (size_t)d);
    uint32_t *rc = malloc(sizeof(uint32_t) * (size_t)N);
    uint32_t *rn = malloc(sizeof(uint32_t) * (size_t)N);
    uint32_t *tmp = malloc(sizeof(uint32_t) * (size_t)N);
    for (int l = 0; l < d; l++) nbr[l] = malloc(sizeof(int) * (size_t)N);

    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) lay[l * k + i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = (int)rnd((uint64_t)(i + 1));
            int t = lay[l * k + i];
            lay[l * k + i] = lay[l * k + j];
            lay[l * k + j] = t;
        }
    }
    for (int q = 0; q < K; q++) S[q] = (int)rnd((uint64_t)GG);
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) set_dart(nbr, lay, S, k, l, i);

    compute_reach(nbr, d, k, N, D, rc, tmp);
    long cost = unreached(rc, k, N) + PENALTY * dupcount(lay, S, d, k);
    double c0 = cost > 1 ? (double)cost : 1.0;
    long best_cost = cost;
    int last = 0;

    for (int t = 0; t < iters && cost != 0; t++) {
        if (elapsed() > g_budget) break;
        if (t - last > patience) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;

        if (k >= 2 && rndf() < 0.25) {
            int l = (int)rnd((uint64_t)d);
            int i1 = (int)rnd((uint64_t)k);
            int i2 = (int)rnd((uint64_t)(k - 1));
            if (i2 >= i1) i2++;
            int tv = lay[l * k + i1];
            lay[l * k + i1] = lay[l * k + i2];
            lay[l * k + i2] = tv;
            set_dart(nbr, lay, S, k, l, i1);
            set_dart(nbr, lay, S, k, l, i2);
            compute_reach(nbr, d, k, N, D, rn, tmp);
            long c2 = unreached(rn, k, N) + PENALTY * dupcount(lay, S, d, k);
            if (c2 <= cost || rndf() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                uint32_t *p = rc;
                rc = rn;
                rn = p;
                if (cost < best_cost) {
                    best_cost = cost;
                    last = t;
                }
            } else {
                tv = lay[l * k + i1];
                lay[l * k + i1] = lay[l * k + i2];
                lay[l * k + i2] = tv;
                set_dart(nbr, lay, S, k, l, i1);
                set_dart(nbr, lay, S, k, l, i2);
            }
            continue;
        }

        int l = 0, i = 0;
        int picked = 0;
        if (rndf() < 0.4) {
            long nbad = 0;
            for (int v = 0; v < N; v++)
                if (rc[v] != full) nbad++;
            if (nbad > 0) {
                long pick = (long)rnd((uint64_t)nbad);
                int u = -1;
                for (int v = 0; v < N; v++) {
                    if (rc[v] != full) {
                        if (pick == 0) {
                            u = v;
                            break;
                        }
                        pick--;
                    }
                }
                int block = u / GG;
                l = (int)rnd((uint64_t)d);
                if (block < k) {
                    i = block;
                } else {
                    i = -1;
                    for (int q = 0; q < k; q++) {
                        if (lay[l * k + q] == block - k) {
                            i = q;
                            break;
                        }
                    }
                    if (i < 0) i = 0;
                }
                picked = 1;
            }
        }
        if (!picked) {
            l = (int)rnd((uint64_t)d);
            i = (int)rnd((uint64_t)k);
        }

        int old = S[l * k + i];
        int nw = (int)rnd((uint64_t)GG);
        if (nw == old) continue;
        S[l * k + i] = nw;
        set_dart(nbr, lay, S, k, l, i);
        compute_reach(nbr, d, k, N, D, rn, tmp);
        long c2 = unreached(rn, k, N) + PENALTY * dupcount(lay, S, d, k);
        if (c2 <= cost || rndf() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            uint32_t *p = rc;
            rc = rn;
            rn = p;
            if (cost < best_cost) {
                best_cost = cost;
                last = t;
            }
        } else {
            S[l * k + i] = old;
            set_dart(nbr, lay, S, k, l, i);
        }
    }

    int ok = (cost == 0);
    if (ok) store_best(nbr, d, k);

    for (int l = 0; l < d; l++) free(nbr[l]);
    free(nbr);
    free(lay);
    free(S);
    free(rc);
    free(rn);
    free(tmp);
    return ok;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: d D seed budget min_n\n");
        return 1;
    }
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    g_rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (g_rs == 0) g_rs = 1;
    for (int w = 0; w < 10; w++) rnext();
    g_budget = atof(argv[4]);
    g_best_n = atol(argv[5]);
    g_t0 = clock();

    if (d < 1 || D < 1) {
        printf("0 0\n");
        return 0;
    }

    long trials[KMAX + 1], wins[KMAX + 1];
    for (int kk = 0; kk <= KMAX; kk++) {
        trials[kk] = 0;
        wins[kk] = 0;
    }

    while (elapsed() < g_budget) {
        int k;
        if (rndf() < 0.2) {
            k = 1 + (int)rnd(KMAX);
        } else {
            double bv = -1.0;
            k = 1;
            for (int kk = 1; kk <= KMAX; kk++) {
                double v = ((double)wins[kk] + 1.0) / ((double)trials[kk] + 2.0) + 0.02 * rndf();
                if (v > bv) {
                    bv = v;
                    k = kk;
                }
            }
        }
        long base = g_best_n / (2L * k);
        long span = base / 8 + 1;
        if (span < 2) span = 2;
        long target = base + 1 + (long)rnd((uint64_t)span);
        if (target < 2) target = 2;

        int m = 0, k2 = 1;
        int64_t r = 1;
        if (!sample_group(target, &m, &k2, &r)) continue;
        set_group(m, k2, r);
        if (2L * k * GG <= g_best_n) continue;

        trials[k]++;
        if (run_trial(d, D, k, 4000, 1200)) wins[k]++;
    }

    if (g_best_m == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%ld %ld\n", g_best_n, g_best_m);
    for (long c = 0; c < g_best_m; c++) {
        printf("%d %d\n", g_edges[2 * c], g_edges[2 * c + 1]);
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Engine B (new, different construction): random d-regular bipartite graph on
# N + N vertices, repaired by degree-preserving edge switches (simulated
# annealing on the number of vertex pairs farther than D apart). Bitset BFS
# evaluates the cost. N is found by bisection: the largest N that succeeds is kept.
# Unlike the bi-Cayley engine, no group structure is imposed.
# ----------------------------------------------------------------------------

RANDREG_C = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static clock_t g_t0;
static double g_budget = 1.0;
static uint64_t g_rs = 0x9E3779B97F4A7C15ULL;
static int g_d = 3, g_D = 3;
static unsigned char g_pc[65536];

static double elapsed(void) {
    return (double)(clock() - g_t0) / (double)CLOCKS_PER_SEC;
}

static uint64_t rnext(void) {
    uint64_t x = g_rs;
    x ^= x >> 12;
    x ^= x << 25;
    x ^= x >> 27;
    g_rs = x;
    return x * 2685821657736338717ULL;
}

static uint64_t rnd(uint64_t n) {
    return n ? rnext() % n : 0;
}

static double rndf(void) {
    return (double)(rnext() >> 11) * (1.0 / 9007199254740992.0);
}

static int popc64(uint64_t x) {
    return g_pc[x & 0xFFFF] + g_pc[(x >> 16) & 0xFFFF] + g_pc[(x >> 32) & 0xFFFF] + g_pc[(x >> 48) & 0xFFFF];
}

typedef struct {
    int N, M, n, W;
    int *ea, *eb;          /* edge e: A-vertex ea[e] to B-vertex eb[e] (both in 0..N-1) */
    unsigned char *mat;    /* N*N adjacency bit matrix */
    int *adj;              /* (2N)*d neighbour lists */
    int *cdeg;
    uint64_t *cur, *nxt;
} St;

static void build_adj(St *s) {
    int d = g_d, N = s->N, n = s->n;
    for (int v = 0; v < n; v++) s->cdeg[v] = 0;
    for (int e = 0; e < s->M; e++) {
        int a = s->ea[e];
        int b = N + s->eb[e];
        s->adj[a * d + s->cdeg[a]++] = b;
        s->adj[b * d + s->cdeg[b]++] = a;
    }
}

/* Number of ordered vertex pairs (v, u) with dist(v, u) > D. */
static long cost(St *s) {
    int n = s->n, W = s->W, d = g_d, D = g_D;
    uint64_t *cur = s->cur, *nxt = s->nxt;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int t = 0; t < D; t++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * (size_t)W);
            for (int k = 0; k < d; k++) {
                const uint64_t *su = cur + (size_t)s->adj[v * d + k] * W;
                for (int w = 0; w < W; w++) dst[w] |= su[w];
            }
        }
        uint64_t *tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    long total = 0;
    size_t tot = (size_t)n * W;
    for (size_t i = 0; i < tot; i++) total += popc64(cur[i]);
    s->cur = cur;
    s->nxt = nxt;
    return (long)n * n - total;
}

/* Best valid graph found so far. */
static long g_best_N = 0;
static int *g_bA = NULL, *g_bB = NULL;

/* Try to build a valid d-regular bipartite graph with N vertices per side. */
static int attempt(int N, double deadline) {
    int d = g_d;
    int M = N * d;
    int n = 2 * N;
    int W = (n + 63) / 64;
    int ok = 0;

    int *ea = malloc(sizeof(int) * (size_t)M);
    int *eb = malloc(sizeof(int) * (size_t)M);
    unsigned char *mat = calloc((size_t)N * (size_t)N, 1);
    unsigned char *bad = calloc((size_t)M, 1);
    int *perm = malloc(sizeof(int) * (size_t)N);
    int *adj = malloc(sizeof(int) * (size_t)n * d);
    int *cdeg = malloc(sizeof(int) * (size_t)n);
    uint64_t *c1 = malloc(sizeof(uint64_t) * (size_t)n * W);
    uint64_t *c2b = malloc(sizeof(uint64_t) * (size_t)n * W);
    if (!ea || !eb || !mat || !bad || !perm || !adj || !cdeg || !c1 || !c2b) goto cleanup;

    St s;
    s.N = N;
    s.M = M;
    s.n = n;
    s.W = W;
    s.ea = ea;
    s.eb = eb;
    s.mat = mat;
    s.adj = adj;
    s.cdeg = cdeg;
    s.cur = c1;
    s.nxt = c2b;

    /* d random perfect matchings, possibly with repeated pairs */
    for (int l = 0; l < d; l++) {
        for (int a = 0; a < N; a++) perm[a] = a;
        for (int a = N - 1; a > 0; a--) {
            int j = (int)rnd((uint64_t)(a + 1));
            int t = perm[a];
            perm[a] = perm[j];
            perm[j] = t;
        }
        for (int a = 0; a < N; a++) {
            int e = l * N + a;
            ea[e] = a;
            eb[e] = perm[a];
        }
    }
    for (int e = 0; e < M; e++) {
        size_t idx = (size_t)ea[e] * N + eb[e];
        if (mat[idx]) bad[e] = 1;
        else mat[idx] = 1;
    }

    /* repair duplicate edges by degree-preserving switches */
    for (int e = 0; e < M; e++) {
        if (!bad[e]) continue;
        int done = 0;
        for (long tries = 0; tries < 2000000 && !done; tries++) {
            int f = (int)rnd((uint64_t)M);
            if (bad[f]) continue;
            int a = ea[e], b = eb[e], c = ea[f], dd = eb[f];
            if (a == c || b == dd) continue;
            mat[(size_t)c * N + dd] = 0;
            if (!mat[(size_t)a * N + dd] && !mat[(size_t)c * N + b]) {
                eb[e] = dd;
                eb[f] = b;
                mat[(size_t)a * N + dd] = 1;
                mat[(size_t)c * N + b] = 1;
                bad[e] = 0;
                done = 1;
            } else {
                mat[(size_t)c * N + dd] = 1;
            }
        }
        if (!done) goto cleanup;
    }

    build_adj(&s);
    long c = cost(&s);
    double t0 = elapsed();
    double span = deadline - t0;
    if (span < 0.05) span = 0.05;
    long it = 0;
    while (c > 0) {
        if ((it & 7) == 0 && elapsed() > deadline) break;
        it++;
        double frac = (elapsed() - t0) / span;
        if (frac < 0.0) frac = 0.0;
        if (frac > 1.0) frac = 1.0;
        double T = 0.5 + 0.02 * (double)c * (1.0 - frac);

        int e = (int)rnd((uint64_t)M);
        int f = (int)rnd((uint64_t)M);
        if (e == f) continue;
        int a = ea[e], b = eb[e], cc = ea[f], dd = eb[f];
        if (a == cc || b == dd) continue;
        if (mat[(size_t)a * N + dd] || mat[(size_t)cc * N + b]) continue;

        mat[(size_t)a * N + b] = 0;
        mat[(size_t)cc * N + dd] = 0;
        mat[(size_t)a * N + dd] = 1;
        mat[(size_t)cc * N + b] = 1;
        eb[e] = dd;
        eb[f] = b;

        build_adj(&s);
        long c2 = cost(&s);
        if (c2 <= c || rndf() < exp(-(double)(c2 - c) / T)) {
            c = c2;
        } else {
            mat[(size_t)a * N + dd] = 0;
            mat[(size_t)cc * N + b] = 0;
            mat[(size_t)a * N + b] = 1;
            mat[(size_t)cc * N + dd] = 1;
            eb[e] = b;
            eb[f] = dd;
        }
    }

    if (c == 0) {
        ok = 1;
        int *nA = malloc(sizeof(int) * (size_t)M);
        int *nB = malloc(sizeof(int) * (size_t)M);
        if (nA && nB) {
            memcpy(nA, ea, sizeof(int) * (size_t)M);
            memcpy(nB, eb, sizeof(int) * (size_t)M);
            free(g_bA);
            free(g_bB);
            g_bA = nA;
            g_bB = nB;
            g_best_N = N;
        } else {
            free(nA);
            free(nB);
            ok = 0;
        }
    }

cleanup:
    free(ea);
    free(eb);
    free(mat);
    free(bad);
    free(perm);
    free(adj);
    free(cdeg);
    free(c1);
    free(c2b);
    return ok;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: d D seed budget N0\n");
        return 1;
    }
    g_d = atoi(argv[1]);
    g_D = atoi(argv[2]);
    g_rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (g_rs == 0) g_rs = 1;
    for (int w = 0; w < 10; w++) rnext();
    g_budget = atof(argv[4]);
    long N0 = atol(argv[5]);
    g_t0 = clock();

    for (int i = 0; i < 65536; i++) {
        int c = 0, x = i;
        while (x) {
            c += x & 1;
            x >>= 1;
        }
        g_pc[i] = (unsigned char)c;
    }

    if (g_d < 2 || g_D < 1) {
        printf("0 0\n");
        return 0;
    }

    /* bisection on N: lo = largest known success, hi = smallest known failure */
    long lo = 0, hi = 0;
    long cur = N0 < g_d ? g_d : N0;
    long step = N0 / 40 + 2;
    while (elapsed() < g_budget - 0.3) {
        double rem = g_budget - elapsed();
        double cap = rem * 0.5;
        if (cap < 2.0) cap = rem;
        int good = attempt((int)cur, elapsed() + cap);
        if (good) {
            lo = cur;
            if (hi == 0) cur += step;
            else cur = (lo + hi) / 2;
            step *= 2;
        } else {
            hi = cur;
            if (lo == 0) {
                cur -= step;
                if (cur < g_d) break;
            } else {
                cur = (lo + hi) / 2;
            }
            step *= 2;
        }
        if (lo && hi && hi - lo <= 1) break;
    }

    if (g_best_N == 0) {
        printf("0 0\n");
        return 0;
    }
    long N = g_best_N;
    long M = N * g_d;
    printf("%ld %ld\n", 2 * N, M);
    for (long e = 0; e < M; e++) {
        printf("%d %d\n", g_bA[e], (int)N + g_bB[e]);
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact and structured baselines.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
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


def _c_run(source, args, timeout):
    """Run a C engine and parse its graph output; returns (n, edges), or (0, []) if nothing found."""
    text = lib.run_c(source, args, timeout=timeout)
    return lib.parse_graph_text(text)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.88 * time_limit, time_limit - 6.0))
    deadline = start + budget

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

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Stage A: bi-Cayley annealing. For D >= 5 it gets 45% of the budget,
    # so that stage B has time to start from its result.
    rem = deadline - time.monotonic()
    if rem > 0.5:
        a_budget = 0.45 * rem if D >= 5 else rem
        timeout = max(1.0, min(a_budget + 3.0, time_limit - (time.monotonic() - start) - 1.5))
        try:
            n, e = _c_run(BICAYLEY_C, [d, D, seed, f"{a_budget:.2f}", best_n], timeout)
            consider(n, e)
        except Exception:
            pass

    # Stage B (new construction): random regular bipartite graph repaired by
    # edge switches, with bisection on the side size. Seeded above the best so far.
    if D >= 5 and d >= 3:
        rem = deadline - time.monotonic()
        if rem > 1.0:
            n0 = best_n // 2 + 1
            b_budget = rem - 0.5
            timeout = max(1.0, min(b_budget + 3.0, time_limit - (time.monotonic() - start) - 1.5))
            try:
                n, e = _c_run(RANDREG_C, [d, D, seed, f"{b_budget:.2f}", n0], timeout)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
