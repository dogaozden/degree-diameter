import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Two engines, combined.
#
# 1. C_SOURCE (group voltage annealing, from the parent) finds a large regular
#    bi-Cayley start graph quickly.
# 2. C_GROW (new, unstructured): takes a regular bipartite graph and grows it by
#    adding vertex pairs. Each pair is wired in by edge splicing, which keeps the
#    graph regular and bipartite. Then it runs simulated annealing with
#    double-edge switches (degree- and bipartiteness-preserving), where the cost
#    is the number of vertex pairs at distance > D, computed with bitset BFS.
#    Whenever the cost reaches 0 the state is saved and the graph grows again.
#
# Every returned graph is checked with lib.is_valid. K_{d,d} is the fallback.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK 4
#define NCHOICE 20
#define PEN 1000

static uint64_t rs;
static uint64_t rnd64(void) {
    uint64_t x = rs;
    x ^= x >> 12;
    x ^= x << 25;
    x ^= x >> 27;
    rs = x;
    return x * 2685821657736338717ULL;
}
static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}
static int rndint(int n) {
    return (int)(rnd64() % (uint64_t)n);
}

static const int K2_CHOICES[NCHOICE] = {1,1,2,2,3,4,5,6,7,8,9,10,12,14,16,18,20,24,30,36};

static int DEG, DIAM, CAP;
static int K, K2, M, R, G, N;
static int64_t PWR[64];
static int *AA, *BB;
static int *nbr, *lay, *vol;
static uint8_t *cur, *scr, *tmpb;
static uint8_t POP[256];
static uint8_t FULL;
static int timed_out;
static double tstart;
static double TL;
static int *bestnbr;
static int best_stride, best_K, best_G;
static int have_best;
static int64_t LASTCOST;

/* Iterated-local-search memory: best near-miss state seen so far. */
static int have_near;
static int nr_K, nr_M, nr_K2, nr_R, nr_G, nr_N;
static int64_t nr_cost;
static int *nr_lay, *nr_vol;

static double elapsed(void) {
    return (double)clock() / CLOCKS_PER_SEC - tstart;
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

static int64_t gcd64(int64_t a, int64_t b) {
    while (b) {
        int64_t t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static int sample_group(int64_t target) {
    for (int attempt = 0; attempt < 200; attempt++) {
        int k2 = K2_CHOICES[rndint(NCHOICE)];
        int64_t m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        int64_t r = -1;
        if (k2 == 1) {
            r = 1;
        } else if (k2 == 2 && rnd01() < 0.3) {
            r = m - 1;
            if (powmod(r, 2, m) != 1 % m) continue;
        } else {
            for (int tries = 0; tries < 60; tries++) {
                int64_t c = (m > 2) ? 2 + rndint((int)(m - 2)) : 1;
                if (gcd64(c, m) == 1 && powmod(c, k2, m) == 1 % m) {
                    r = c;
                    break;
                }
            }
            if (r < 0) continue;
        }
        M = (int)m;
        K2 = k2;
        R = (int)r;
        G = M * K2;
        return 1;
    }
    return 0;
}

static void setup_group(void) {
    for (int t = 0; t < K2; t++) PWR[t] = powmod(R, t, M);
    for (int x = 0; x < G; x++) {
        AA[x] = x / K2;
        BB[x] = x % K2;
    }
}

/* (a,b)(c,e) = (a + r^b c, b + e) */
static inline int gmul(int x, int y) {
    int bx = BB[x];
    int64_t a2 = (AA[x] + PWR[bx] * (int64_t)AA[y]) % M;
    int b2 = (bx + BB[y]) % K2;
    return (int)(a2 * K2 + b2);
}

/* inverse of (a,b) is (-r^{-b} a, -b) */
static inline int ginv(int x) {
    int b = BB[x];
    int nb = (K2 - b) % K2;
    int64_t a2 = (M - (PWR[nb] * (int64_t)AA[x]) % M) % M;
    return (int)(a2 * K2 + nb);
}

static void set_dart(int l, int i, int p, int s) {
    int is = ginv(s);
    int *row = nbr + (size_t)l * N;
    int Ab = i * G, Bb = (K + p) * G;
    for (int g = 0; g < G; g++) {
        row[Ab + g] = Bb + gmul(g, s);
        row[Bb + g] = Ab + gmul(g, is);
    }
}

static void compute_reach(uint8_t *out) {
    memset(out, 0, (size_t)N);
    for (int b = 0; b < 2 * K; b++) out[b * G] = (uint8_t)(1u << b);
    for (int t = 0; t < DIAM; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint8_t x = out[v];
            for (int l = 0; l < DEG; l++) x |= out[nbr[(size_t)l * N + v]];
            tmpb[v] = x;
            if (x != out[v]) changed = 1;
        }
        if (!changed) break;
        memcpy(out, tmpb, (size_t)N);
    }
}

static int64_t unreached(const uint8_t *r) {
    int64_t s = 0;
    for (int v = 0; v < N; v++) s += POP[r[v]];
    return (int64_t)2 * K * N - s;
}

static int dupcount(void) {
    int n = DEG * K, dup = 0;
    for (int e = 0; e < n; e++) {
        int i = e % K;
        for (int f = i; f < e; f += K) {
            if (lay[f] == lay[e] && vol[f] == vol[e]) {
                dup++;
                break;
            }
        }
    }
    return dup;
}

static int64_t total_cost(const uint8_t *r) {
    return unreached(r) + (int64_t)PEN * dupcount();
}

/* reinit = 1: random permutations and voltages. reinit = 0: continue from the
   current lay/vol state (every rejected move was reverted, so it is consistent). */
static int run_trial(int iters, int patience, int reinit) {
    int n = DEG * K;
    timed_out = 0;
    if (reinit) {
        for (int l = 0; l < DEG; l++) {
            int perm[MAXK];
            for (int i = 0; i < K; i++) perm[i] = i;
            for (int i = K - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int t = perm[i];
                perm[i] = perm[j];
                perm[j] = t;
            }
            for (int i = 0; i < K; i++) lay[l * K + i] = perm[i];
        }
        for (int e = 0; e < n; e++) vol[e] = rndint(G);
    }
    for (int l = 0; l < DEG; l++)
        for (int i = 0; i < K; i++)
            set_dart(l, i, lay[l * K + i], vol[l * K + i]);

    compute_reach(cur);
    int64_t cost = total_cost(cur);
    double c0 = cost > 1 ? (double)cost : 1.0;
    int64_t best_cost = cost;
    int last = 0;

    for (int t = 0; t < iters && cost != 0; t++) {
        if (t - last > patience) break;
        if ((t & 31) == 0 && elapsed() > TL) {
            timed_out = 1;
            break;
        }
        double temp = 0.01 * c0 * (1.0 - (double)t / iters);
        if (temp < 0.5) temp = 0.5;
        int64_t c2 = 0;

        if (K >= 2 && rnd01() < 0.25) {
            /* layer-swap move */
            int l = rndint(DEG);
            int i1 = rndint(K);
            int i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int e1 = l * K + i1, e2 = l * K + i2;
            int tp = lay[e1];
            lay[e1] = lay[e2];
            lay[e2] = tp;
            set_dart(l, i1, lay[e1], vol[e1]);
            set_dart(l, i2, lay[e2], vol[e2]);
            compute_reach(scr);
            c2 = total_cost(scr);
            if (!(c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp))) {
                tp = lay[e1];
                lay[e1] = lay[e2];
                lay[e2] = tp;
                set_dart(l, i1, lay[e1], vol[e1]);
                set_dart(l, i2, lay[e2], vol[e2]);
                continue;
            }
        } else {
            /* voltage move, defect-targeted with probability 0.4 */
            int l = 0, i = 0, u = -1;
            if (rnd01() < 0.4) {
                int cnt = 0;
                for (int v = 0; v < N; v++) {
                    if (cur[v] != FULL) {
                        cnt++;
                        if (rndint(cnt) == 0) u = v;
                    }
                }
            }
            if (u >= 0) {
                int block = u / G;
                l = rndint(DEG);
                i = -1;
                if (block < K) {
                    i = block;
                } else {
                    for (int j = 0; j < K; j++) {
                        if (lay[l * K + j] == block - K) {
                            i = j;
                            break;
                        }
                    }
                }
                if (i < 0) continue;
            } else {
                l = rndint(DEG);
                i = rndint(K);
            }
            int e = l * K + i;
            int old = vol[e];
            int nw = rndint(G);
            if (nw == old) continue;
            vol[e] = nw;
            set_dart(l, i, lay[e], nw);
            compute_reach(scr);
            c2 = total_cost(scr);
            if (!(c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp))) {
                vol[e] = old;
                set_dart(l, i, lay[e], old);
                continue;
            }
        }

        /* accepted */
        uint8_t *tb = cur;
        cur = scr;
        scr = tb;
        cost = c2;
        if (cost < best_cost) {
            best_cost = cost;
            last = t;
        }
    }
    LASTCOST = cost;
    return cost == 0;
}

/* Save the current (consistent) lay/vol state and its group as the near-miss memory. */
static void save_near(void) {
    have_near = 1;
    nr_K = K;
    nr_M = M;
    nr_K2 = K2;
    nr_R = R;
    nr_G = G;
    nr_N = N;
    nr_cost = LASTCOST;
    memcpy(nr_lay, lay, sizeof(int) * (size_t)DEG * MAXK);
    memcpy(nr_vol, vol, sizeof(int) * (size_t)DEG * MAXK);
}

static int pick_k(const double *tr, const double *wn) {
    if (rnd01() < 0.2) return 1 + rndint(MAXK);
    int bk = 1;
    double bv = -1.0;
    for (int k = 1; k <= MAXK; k++) {
        double v = (wn[k] + 1.0) / (tr[k] + 2.0) + 0.02 * rnd01();
        if (v > bv) {
            bv = v;
            bk = k;
        }
    }
    return bk;
}

int main(int argc, char **argv) {
    if (argc < 7) {
        fprintf(stderr, "usage: d D target cap seed time\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    long long best0 = atoll(argv[3]);
    CAP = atoi(argv[4]);
    unsigned long long seed = strtoull(argv[5], NULL, 10);
    TL = atof(argv[6]);
    tstart = (double)clock() / CLOCKS_PER_SEC;

    rs = (seed + 1) * 0x9E3779B97F4A7C15ULL ^ 0xD1B54A32D192ED03ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();
    for (int x = 0; x < 256; x++) {
        int c = 0;
        for (int y = x; y; y >>= 1) c += y & 1;
        POP[x] = (uint8_t)c;
    }

    if (DEG < 3 || DIAM < 3 || CAP < 8) {
        printf("0 0\n");
        return 0;
    }

    AA = malloc(sizeof(int) * (size_t)(CAP + 1));
    BB = malloc(sizeof(int) * (size_t)(CAP + 1));
    nbr = malloc(sizeof(int) * (size_t)DEG * CAP);
    lay = malloc(sizeof(int) * (size_t)DEG * MAXK);
    vol = malloc(sizeof(int) * (size_t)DEG * MAXK);
    nr_lay = malloc(sizeof(int) * (size_t)DEG * MAXK);
    nr_vol = malloc(sizeof(int) * (size_t)DEG * MAXK);
    cur = malloc((size_t)CAP);
    scr = malloc((size_t)CAP);
    tmpb = malloc((size_t)CAP);
    bestnbr = malloc(sizeof(int) * (size_t)DEG * CAP);
    if (!AA || !BB || !nbr || !lay || !vol || !nr_lay || !nr_vol || !cur || !scr ||
        !tmpb || !bestnbr) {
        printf("0 0\n");
        return 0;
    }

    double tr[MAXK + 1] = {0}, wn[MAXK + 1] = {0};
    long long found = best0;

    while (elapsed() < TL) {
        if (found >= CAP) break;
        int k = 1;
        int ok = 0;

        if (have_near && nr_N > found && rnd01() < 0.5) {
            /* Iterated local search: kick the saved near-miss state and re-anneal it. */
            k = nr_K;
            K = nr_K;
            M = nr_M;
            K2 = nr_K2;
            R = nr_R;
            G = nr_G;
            N = nr_N;
            FULL = (uint8_t)((1u << (2 * K)) - 1);
            setup_group();
            memcpy(lay, nr_lay, sizeof(int) * (size_t)DEG * MAXK);
            memcpy(vol, nr_vol, sizeof(int) * (size_t)DEG * MAXK);
            int kicks = 2 + rndint(4);
            for (int q = 0; q < kicks; q++) {
                int l = rndint(DEG), i = rndint(K);
                vol[l * K + i] = rndint(G);
            }
            ok = run_trial(3000, 1000, 0);
        } else {
            k = pick_k(tr, wn);
            int64_t base = found / (2 * k);
            int64_t span = base / 8 + 1;
            if (span < 2) span = 2;
            int64_t target = base + 1 + rndint((int)span);
            if (target < 2) target = 2;
            if (!sample_group(target)) continue;
            long long Nn = 2LL * k * G;
            if (Nn <= found || Nn > CAP) continue;

            K = k;
            N = (int)Nn;
            FULL = (uint8_t)((1u << (2 * K)) - 1);
            setup_group();
            tr[k] += 1.0;
            ok = run_trial(4000, 1200, 1);
        }

        /* Near miss: keep annealing the same group from its final state. */
        int extra = 0;
        while (!ok && !timed_out && extra < 3 && LASTCOST <= (int64_t)N / 2 && elapsed() < TL) {
            ok = run_trial(6000, 2000, 0);
            extra++;
        }

        /* Remember the best unsuccessful state for later kicks. */
        if (!ok && !timed_out && LASTCOST > 0) {
            if (!have_near || LASTCOST < nr_cost || nr_N <= found) save_near();
        }

        if (ok) {
            wn[k] += 1.0;
            found = N;
            memcpy(bestnbr, nbr, sizeof(int) * (size_t)DEG * N);
            best_stride = N;
            best_K = K;
            best_G = G;
            have_best = 1;
            have_near = 0;
        }
        if (timed_out) break;
    }

    if (!have_best) {
        printf("0 0\n");
        return 0;
    }
    int KG = best_K * best_G;
    long long m = (long long)KG * DEG;
    printf("%d %lld\n", best_stride, m);
    for (int u = 0; u < KG; u++)
        for (int l = 0; l < DEG; l++)
            printf("%d %d\n", u, bestnbr[(size_t)l * best_stride + u]);
    return 0;
}
"""


C_GROW = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static uint64_t rs;
static uint64_t rnd64(void) {
    uint64_t x = rs;
    x ^= x >> 12;
    x ^= x << 25;
    x ^= x >> 27;
    rs = x;
    return x * 2685821657736338717ULL;
}
static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}
static int rndint(int n) {
    return (int)(rnd64() % (uint64_t)n);
}

static int DEG, DIAM, CAP, CAPW;
static int N, NE, W;
static int *nbr, *deg, *col, *ea, *eb, *bestA, *bestB;
static uint64_t *cur, *nxt;
static int bestN, bestNE;
static int broken;
static double tstart, TL;

static double elapsed(void) {
    return (double)clock() / CLOCKS_PER_SEC - tstart;
}

static inline int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void reset_pair(int x) {
    for (int i = 0; i < DEG; i++) nbr[(size_t)x * DEG + i] = -1;
    deg[x] = 0;
}

static int has_nbr(int v, int u) {
    const int *p = nbr + (size_t)v * DEG;
    for (int i = 0; i < DEG; i++)
        if (p[i] == u) return 1;
    return 0;
}

static void rep_nbr(int v, int old, int nw) {
    int *p = nbr + (size_t)v * DEG;
    for (int i = 0; i < DEG; i++) {
        if (p[i] == old) {
            p[i] = nw;
            return;
        }
    }
}

/* Number of ordered-free unreached unordered pairs (distance > DIAM). */
static int64_t cost_full(void) {
    W = (N + 63) >> 6;
    size_t sz = (size_t)N * (size_t)W;
    memset(cur, 0, sizeof(uint64_t) * sz);
    for (int v = 0; v < N; v++)
        cur[(size_t)v * W + (size_t)(v >> 6)] |= 1ULL << (v & 63);
    for (int t = 0; t < DIAM; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            const uint64_t *s = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) o[w] = s[w];
            const int *p = nbr + (size_t)v * DEG;
            for (int i = 0; i < DEG; i++) {
                const uint64_t *q = cur + (size_t)p[i] * W;
                for (int w = 0; w < W; w++) o[w] |= q[w];
            }
            for (int w = 0; w < W; w++) {
                if (o[w] != s[w]) {
                    changed = 1;
                    break;
                }
            }
        }
        uint64_t *tmp = cur;
        cur = nxt;
        nxt = tmp;
        if (!changed) break;
    }
    int64_t reached = 0;
    for (size_t i = 0; i < sz; i++) reached += pc64(cur[i]);
    return ((int64_t)N * N - reached) / 2;
}

static void save_best(void) {
    bestN = N;
    bestNE = NE;
    memcpy(bestA, ea, sizeof(int) * (size_t)NE);
    memcpy(bestB, eb, sizeof(int) * (size_t)NE);
}

static void build_kdd(void) {
    N = 2 * DEG;
    NE = 0;
    for (int v = 0; v < N; v++) reset_pair(v);
    for (int a = 0; a < DEG; a++) {
        col[a] = 0;
        col[DEG + a] = 1;
    }
    for (int a = 0; a < DEG; a++) {
        for (int b = 0; b < DEG; b++) {
            int x = a, y = DEG + b;
            nbr[(size_t)x * DEG + deg[x]++] = y;
            nbr[(size_t)y * DEG + deg[y]++] = x;
            ea[NE] = x;
            eb[NE] = y;
            NE++;
        }
    }
}

static int load_graph(void) {
    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n < 2 || n > CAP || m < 1 || 2 * m != DEG * n) return 0;
    int *eu = malloc(sizeof(int) * (size_t)(2 * m));
    int *dg = calloc((size_t)n, sizeof(int));
    int *q = malloc(sizeof(int) * (size_t)n);
    if (!eu || !dg || !q) {
        free(eu);
        free(dg);
        free(q);
        return 0;
    }
    int ok = 1;
    for (int i = 0; i < m && ok; i++) {
        int u = -1, v = -1;
        if (scanf("%d %d", &u, &v) != 2) {
            ok = 0;
        } else if (u < 0 || v < 0 || u >= n || v >= n || u == v) {
            ok = 0;
        } else {
            eu[2 * i] = u;
            eu[2 * i + 1] = v;
            dg[u]++;
            dg[v]++;
        }
    }
    for (int v = 0; v < n && ok; v++)
        if (dg[v] != DEG) ok = 0;
    if (ok) {
        N = n;
        for (int v = 0; v < n; v++) reset_pair(v);
        for (int i = 0; i < m && ok; i++) {
            int u = eu[2 * i], v = eu[2 * i + 1];
            if (has_nbr(u, v)) {
                ok = 0;
            } else {
                nbr[(size_t)u * DEG + deg[u]++] = v;
                nbr[(size_t)v * DEG + deg[v]++] = u;
            }
        }
    }
    if (ok) {
        for (int v = 0; v < n; v++) col[v] = -1;
        for (int s = 0; s < n && ok; s++) {
            if (col[s] >= 0) continue;
            int qh = 0, qt = 0;
            col[s] = 0;
            q[qt++] = s;
            while (qh < qt && ok) {
                int u = q[qh++];
                for (int i = 0; i < DEG; i++) {
                    int w = nbr[(size_t)u * DEG + i];
                    if (col[w] < 0) {
                        col[w] = 1 - col[u];
                        q[qt++] = w;
                    } else if (col[w] == col[u]) {
                        ok = 0;
                        break;
                    }
                }
            }
        }
    }
    if (ok) {
        NE = 0;
        for (int i = 0; i < m; i++) {
            int u = eu[2 * i], v = eu[2 * i + 1];
            if (col[u] == 0) {
                ea[NE] = u;
                eb[NE] = v;
            } else {
                ea[NE] = v;
                eb[NE] = u;
            }
            NE++;
        }
    }
    free(eu);
    free(dg);
    free(q);
    return ok;
}

/* Add vertex pair (x in A, y in B) of full degree DEG by splicing existing edges:
   edge (a,b) becomes (a,y) and (x,b); each splice adds one degree to x and y. */
static void fill_pair(int x, int y) {
    for (int k = 0; k < DEG; k++) {
        int done = 0;
        for (int tries = 0; tries < 400000 && !done; tries++) {
            int e = rndint(NE);
            int a = ea[e], b = eb[e];
            if (a == x || b == y) continue;
            if (has_nbr(a, y) || has_nbr(x, b)) continue;
            rep_nbr(a, b, y);
            rep_nbr(b, a, x);
            nbr[(size_t)x * DEG + deg[x]++] = b;
            nbr[(size_t)y * DEG + deg[y]++] = a;
            eb[e] = y;
            ea[NE] = x;
            eb[NE] = b;
            NE++;
            done = 1;
        }
        if (!done) {
            broken = 1;
            return;
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 6) return 1;
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    CAP = atoi(argv[3]);
    unsigned long long seed = strtoull(argv[4], NULL, 10);
    TL = atof(argv[5]);
    tstart = (double)clock() / CLOCKS_PER_SEC;

    rs = (seed + 1) * 0x9E3779B97F4A7C15ULL ^ 0xA24BAED4963EE407ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();

    if (DEG < 3 || DIAM < 3 || CAP < 2 * DEG + 4) {
        printf("0 0\n");
        return 0;
    }
    CAPW = (CAP + 63) >> 6;
    size_t cap2 = (size_t)CAP + 4;
    nbr = malloc(sizeof(int) * (size_t)DEG * cap2);
    deg = malloc(sizeof(int) * cap2);
    col = malloc(sizeof(int) * cap2);
    ea = malloc(sizeof(int) * (size_t)DEG * cap2);
    eb = malloc(sizeof(int) * (size_t)DEG * cap2);
    bestA = malloc(sizeof(int) * (size_t)DEG * cap2);
    bestB = malloc(sizeof(int) * (size_t)DEG * cap2);
    cur = malloc(sizeof(uint64_t) * cap2 * (size_t)CAPW);
    nxt = malloc(sizeof(uint64_t) * cap2 * (size_t)CAPW);
    if (!nbr || !deg || !col || !ea || !eb || !bestA || !bestB || !cur || !nxt) {
        printf("0 0\n");
        return 0;
    }
    for (size_t i = 0; i < (size_t)DEG * cap2; i++) nbr[i] = -1;

    bestN = 0;
    bestNE = 0;
    int loaded = load_graph();
    int64_t cost = loaded ? cost_full() : 1;
    if (!loaded || cost != 0) {
        build_kdd();
        cost = cost_full();
    }
    if (cost == 0) save_best();

    int step = 1;
    long long since = 0;
    long long iter = 0;
    while (1) {
        if ((iter & 15) == 0 && elapsed() > TL) break;
        iter++;
        if (cost == 0) {
            save_best();
            if (since < 40) step = step + step / 4 + 1;
            else if (since > 400 && step > 1) step = (step * 3) / 4;
            since = 0;
            int s = step;
            if (N + 2 * s > CAP) s = (CAP - N) / 2;
            if (s < 1) break;
            for (int j = 0; j < s && !broken; j++) {
                int x = N, y = N + 1;
                col[x] = 0;
                col[y] = 1;
                reset_pair(x);
                reset_pair(y);
                N += 2;
                fill_pair(x, y);
            }
            if (broken) break;
            cost = cost_full();
            continue;
        }

        /* Double-edge switch: (a,b),(c,d) -> (a,d),(c,b). */
        int e1 = rndint(NE), e2 = rndint(NE);
        if (e1 == e2) continue;
        int a = ea[e1], b = eb[e1], c = ea[e2], dd = eb[e2];
        if (a == c || b == dd) continue;
        if (has_nbr(a, dd) || has_nbr(c, b)) continue;
        rep_nbr(a, b, dd);
        rep_nbr(b, a, c);
        rep_nbr(c, dd, b);
        rep_nbr(dd, c, a);
        ea[e1] = a;
        eb[e1] = dd;
        ea[e2] = c;
        eb[e2] = b;
        int64_t nc = cost_full();
        since++;
        double T = 0.3 + 0.0015 * (double)cost;
        int64_t delta = nc - cost;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cost = nc;
        } else {
            rep_nbr(a, dd, b);
            rep_nbr(b, c, a);
            rep_nbr(c, b, dd);
            rep_nbr(dd, a, c);
            ea[e1] = a;
            eb[e1] = b;
            ea[e2] = c;
            eb[e2] = dd;
        }
    }

    printf("%d %d\n", bestN, bestNE);
    for (int i = 0; i < bestNE; i++) printf("%d %d\n", bestA[i], bestB[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact constructions used as the start graph.
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


# ----------------------------------------------------------------------------
# Main build: exact constructions, then group voltage search, then edge-switch growth.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} is d-regular, bipartite and has diameter 2.
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
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D == 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    if d >= 3 and D >= 3:
        seed_arg = int(seed) & 0x7FFFFFFF
        moore = lib.moore_bound(d, D)

        # Stage 1: group voltage search gives a large regular bipartite start.
        rem = deadline - time.monotonic()
        if rem > 4.0:
            s1 = 0.4 * rem
            try:
                text = lib.run_c(C_SOURCE,
                                 [d, D, best_n, moore, seed_arg, round(s1, 2)],
                                 timeout=s1 + 3.0)
                consider(*lib.parse_graph_text(text))
            except Exception:
                pass

        # Stage 2: edge-switch annealing that grows the current best regular graph.
        rem = deadline - time.monotonic()
        if rem > 2.0:
            cap = min(moore, 8000)
            try:
                text = lib.run_c(C_GROW,
                                 [d, D, cap, seed_arg, round(rem - 0.5, 2)],
                                 stdin_graph=best,
                                 timeout=rem + 3.0)
                consider(*lib.parse_graph_text(text))
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
