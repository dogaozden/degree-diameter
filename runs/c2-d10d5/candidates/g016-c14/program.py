import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Stage 1 C engine (unchanged from parent): bi-Cayley voltage annealing over
# Z_m x| Z_k2. Vertices: A_{i,g} = i*G + g, B_{p,h} = (K+p)*G + h. Each layer
# is a permutation, so every vertex has degree DEG exactly. Cost = unreached
# pairs + penalty * duplicate keys. Cost 0 gives a valid simple bipartite graph.
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
    cur = malloc((size_t)CAP);
    scr = malloc((size_t)CAP);
    tmpb = malloc((size_t)CAP);
    bestnbr = malloc(sizeof(int) * (size_t)DEG * CAP);
    if (!AA || !BB || !nbr || !lay || !vol || !cur || !scr || !tmpb || !bestnbr) {
        printf("0 0\n");
        return 0;
    }

    double tr[MAXK + 1] = {0}, wn[MAXK + 1] = {0};
    long long found = best0;

    while (elapsed() < TL) {
        if (found >= CAP) break;
        int k = pick_k(tr, wn);
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
        int ok = run_trial(4000, 1200, 1);
        /* Near miss: keep annealing the same group from its final state. */
        int extra = 0;
        while (!ok && !timed_out && extra < 6 && LASTCOST <= (int64_t)N / 4 && elapsed() < TL) {
            ok = run_trial(6000, 1500, 0);
            extra++;
        }
        if (ok) {
            wn[k] += 1.0;
            found = N;
            memcpy(bestnbr, nbr, sizeof(int) * (size_t)DEG * N);
            best_stride = N;
            best_K = K;
            best_G = G;
            have_best = 1;
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


# ----------------------------------------------------------------------------
# Stage 2 C engine (new, substantially different construction).
#
# Works on ARBITRARY d-regular bipartite graphs, not lifts. Two moves:
#   * Vertex-pair insertion ("edge split"): choose d edges (x_i, y_i) with
#     distinct x_i (side 0) and distinct y_i (side 1). Add a new side-0 vertex a
#     joined to all y_i and a new side-1 vertex b joined to all x_i, removing
#     the x_i y_i edges. Every degree stays d and the graph stays bipartite.
#   * Edge switch: (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). Degrees are preserved.
# Cost = ordered pairs at distance > DIAM (computed with bitset BFS). Annealing
# runs on the current graph. When cost hits 0 the graph is snapshotted and
# another pair is inserted. After STALL non-improving moves the engine restores
# the last valid snapshot and inserts a different pair.
# Output: the largest valid snapshot, in the standard text format.
# Untested in this session: the speed (about one full bitset BFS per move)
# is the main risk, so it may gain little within the time limit.
# ----------------------------------------------------------------------------

C_EDGE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 64
#define STALL 1000

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
static int rndint(int m) {
    return (int)(rnd64() % (uint64_t)m);
}

static int DEG, DIAM, CAP, W, n, vn;
static int *nb, *vnb;
static unsigned char *side;
static uint64_t *RA, *RB;
static double TL, tstart;
static int sa1, sk1, sa2, sk2, sb1, sb2;

static double elapsed(void) {
    return (double)clock() / CLOCKS_PER_SEC - tstart;
}

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of ordered pairs (v,u) with dist(v,u) > DIAM. */
static long long evalcost(void) {
    uint64_t *cur = RA, *nxt = RB;
    size_t tot = (size_t)n * W;
    memset(cur, 0, tot * sizeof(uint64_t));
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int t = 0; t < DIAM; t++) {
        for (int v = 0; v < n; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            const uint64_t *s = cur + (size_t)v * W;
            memcpy(o, s, (size_t)W * sizeof(uint64_t));
            for (int k = 0; k < DEG; k++) {
                const uint64_t *su = cur + (size_t)nb[v * DEG + k] * W;
                for (int w = 0; w < W; w++) o[w] |= su[w];
            }
        }
        uint64_t *tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    long long cnt = 0;
    for (size_t i = 0; i < tot; i++) cnt += pc64(cur[i]);
    return (long long)n * n - cnt;
}

static int has_edge(int v, int u) {
    for (int k = 0; k < DEG; k++)
        if (nb[v * DEG + k] == u) return 1;
    return 0;
}

static void replace_in(int v, int oldu, int newu) {
    for (int k = 0; k < DEG; k++) {
        if (nb[v * DEG + k] == oldu) {
            nb[v * DEG + k] = newu;
            return;
        }
    }
}

/* Edge-split insertion of two new vertices a (side 0) and b (side 1). */
static int insert_pair(void) {
    int xs[MAXD], ks[MAXD], ys[MAXD];
    int cnt = 0;
    if (n + 2 > CAP) return 0;
    for (int att = 0; att < 400 && cnt < DEG; att++) {
        int x = rndint(n);
        if (side[x] != 0) continue;
        int k = rndint(DEG);
        int y = nb[x * DEG + k];
        int bad = 0;
        for (int i = 0; i < cnt; i++) {
            if (xs[i] == x || ys[i] == y) {
                bad = 1;
                break;
            }
        }
        if (bad) continue;
        xs[cnt] = x;
        ks[cnt] = k;
        ys[cnt] = y;
        cnt++;
    }
    if (cnt < DEG) return 0;
    int a = n, b = n + 1;
    side[a] = 0;
    side[b] = 1;
    for (int i = 0; i < DEG; i++) {
        int x = xs[i], k = ks[i], y = ys[i];
        nb[x * DEG + k] = b;
        for (int j = 0; j < DEG; j++) {
            if (nb[y * DEG + j] == x) {
                nb[y * DEG + j] = a;
                break;
            }
        }
        nb[a * DEG + i] = y;
        nb[b * DEG + i] = x;
    }
    n += 2;
    return 1;
}

static int try_switch(void) {
    int a1, a2, k1, k2, b1, b2;
    do {
        a1 = rndint(n);
    } while (side[a1] != 0);
    do {
        a2 = rndint(n);
    } while (side[a2] != 0);
    if (a1 == a2) return 0;
    k1 = rndint(DEG);
    k2 = rndint(DEG);
    b1 = nb[a1 * DEG + k1];
    b2 = nb[a2 * DEG + k2];
    if (b1 == b2) return 0;
    if (has_edge(a1, b2) || has_edge(a2, b1)) return 0;
    nb[a1 * DEG + k1] = b2;
    nb[a2 * DEG + k2] = b1;
    replace_in(b1, a1, a2);
    replace_in(b2, a2, a1);
    sa1 = a1;
    sk1 = k1;
    sa2 = a2;
    sk2 = k2;
    sb1 = b1;
    sb2 = b2;
    return 1;
}

static void undo_switch(void) {
    nb[sa1 * DEG + sk1] = sb1;
    nb[sa2 * DEG + sk2] = sb2;
    replace_in(sb1, sa2, sa1);
    replace_in(sb2, sa1, sa2);
}

int main(int argc, char **argv) {
    if (argc < 6) {
        printf("0 0\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    CAP = atoi(argv[3]);
    unsigned long long seed = strtoull(argv[4], NULL, 10);
    TL = atof(argv[5]);
    tstart = (double)clock() / CLOCKS_PER_SEC;

    rs = (seed + 1) * 0x9E3779B97F4A7C15ULL ^ 0xA0761D6478BD642FULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || DEG < 3 || DEG > MAXD || n0 < 2 ||
        CAP < n0 + 2 || m0 < 0) {
        printf("0 0\n");
        return 0;
    }
    int *eu = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *ev = malloc(sizeof(int) * (size_t)(m0 + 1));
    if (!eu || !ev) {
        printf("0 0\n");
        return 0;
    }
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) {
            printf("0 0\n");
            return 0;
        }
    }

    nb = malloc(sizeof(int) * (size_t)CAP * DEG);
    vnb = malloc(sizeof(int) * (size_t)CAP * DEG);
    side = malloc((size_t)CAP);
    int *deg = calloc((size_t)CAP, sizeof(int));
    int *queue = malloc(sizeof(int) * (size_t)CAP);
    if (!nb || !vnb || !side || !deg || !queue) {
        printf("0 0\n");
        return 0;
    }
    for (size_t i = 0; i < (size_t)CAP * DEG; i++) nb[i] = -1;
    memset(side, 255, (size_t)CAP);

    int ok = 1;
    for (int i = 0; i < m0 && ok; i++) {
        int u = eu[i], v = ev[i];
        if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) {
            ok = 0;
            break;
        }
        if (deg[u] >= DEG || deg[v] >= DEG) {
            ok = 0;
            break;
        }
        nb[u * DEG + deg[u]++] = v;
        nb[v * DEG + deg[v]++] = u;
    }
    for (int v = 0; v < n0 && ok; v++)
        if (deg[v] != DEG) ok = 0;

    /* Bipartition by BFS. */
    for (int s = 0; s < n0 && ok; s++) {
        if (side[s] != 255) continue;
        side[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt && ok) {
            int u = queue[qh++];
            for (int k = 0; k < DEG; k++) {
                int v = nb[u * DEG + k];
                if (side[v] == 255) {
                    side[v] = 1 - side[u];
                    queue[qt++] = v;
                } else if (side[v] == side[u]) {
                    ok = 0;
                    break;
                }
            }
        }
    }
    if (!ok) {
        printf("0 0\n");
        return 0;
    }

    n = n0;
    W = (CAP + 63) / 64;
    RA = malloc((size_t)CAP * W * sizeof(uint64_t));
    RB = malloc((size_t)CAP * W * sizeof(uint64_t));
    if (!RA || !RB) {
        printf("0 0\n");
        return 0;
    }

    vn = n0;
    memcpy(vnb, nb, sizeof(int) * (size_t)n0 * DEG);
    long long cost = evalcost();
    if (cost != 0) {
        printf("0 0\n");
        return 0;
    }

    int stall = 0;
    while (elapsed() < TL) {
        if (cost == 0) {
            vn = n;
            memcpy(vnb, nb, sizeof(int) * (size_t)n * DEG);
            stall = 0;
            if (!insert_pair()) break;
            cost = evalcost();
            continue;
        }
        if (stall > STALL) {
            /* Restore the last valid snapshot, then insert a different pair. */
            n = vn;
            memcpy(nb, vnb, sizeof(int) * (size_t)n * DEG);
            stall = 0;
            cost = 0;
            continue;
        }
        if (!try_switch()) {
            stall++;
            continue;
        }
        long long c2 = evalcost();
        double T = 1.5 * (1.0 - (double)stall / STALL) + 0.05;
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
            if (c2 < cost) stall = 0;
            else stall++;
            cost = c2;
        } else {
            undo_switch();
            stall++;
        }
    }

    int na = 0;
    for (int v = 0; v < vn; v++)
        if (side[v] == 0) na++;
    printf("%d %d\n", vn, na * DEG);
    for (int v = 0; v < vn; v++) {
        if (side[v] != 0) continue;
        for (int k = 0; k < DEG; k++)
            printf("%d %d\n", v, vnb[v * DEG + k]);
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Safe exact families.
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
# Slack extension: add new vertices using spare degree (only if any exists).
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """Return the 2-colouring of the graph, or None if it is not bipartite."""
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
                elif color[v] == color[u]:
                    return None
    return color


def _slack_extend(n, edges, d, D, rng, deadline):
    """Greedily add new vertices using spare degree; returns (n, edges), always valid."""
    edges = [tuple(e) for e in edges]
    adj = lib.adjacency(n, edges)
    color = _bipartition(n, adj)
    if color is None:
        return n, edges
    deg = [len(a) for a in adj]
    grew = True
    while grew and time.monotonic() < deadline:
        grew = False
        for side in (0, 1):
            spare = [v for v in range(n) if color[v] == side and deg[v] < d]
            if len(spare) < d:
                continue
            for _ in range(30):
                if time.monotonic() > deadline or len(spare) < d:
                    break
                pick = rng.sample(spare, d)
                w = n
                cand = edges + [(v, w) for v in pick]
                if lib.is_valid(n + 1, cand, d, D):
                    edges = cand
                    n += 1
                    color.append(1 - side)
                    deg.append(d)
                    for v in pick:
                        deg[v] += 1
                    spare = [v for v in spare if deg[v] < d]
                    grew = True
                    break
    return n, edges


# ----------------------------------------------------------------------------
# Main build: exact constructions, then voltage lift search (stage 1), then
# edge-level annealing growth from the best graph (stage 2), then slack.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 8.0))
    final_deadline = start + max(1.0, time_limit - 3.0)
    rng = random.Random(seed)

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

    if D >= 4 and time.monotonic() < start + budget:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    if d >= 3 and D >= 3:
        # Stage 1: voltage-lift search.
        remaining = start + budget - time.monotonic()
        if remaining > 2.0:
            cap = lib.moore_bound(d, D)
            split = remaining * 0.55 if remaining > 10.0 else remaining
            try:
                text = lib.run_c(C_SOURCE,
                                 [d, D, best_n, cap, int(seed) & 0x7FFFFFFF, round(split, 2)],
                                 timeout=split + 20.0)
                n2, e2 = lib.parse_graph_text(text)
                consider(n2, e2)
            except Exception:
                pass

        # Stage 2: edge-level annealing growth from the best regular graph.
        remaining2 = start + budget - time.monotonic()
        if remaining2 > 3.0:
            cap2 = min(lib.moore_bound(d, D), best_n + max(200, best_n // 3))
            try:
                text = lib.run_c(C_EDGE,
                                 [d, D, cap2, int(seed) & 0x7FFFFFFF, round(remaining2, 2)],
                                 stdin_graph=(best[0], best[1]),
                                 timeout=remaining2 + 20.0)
                n3, e3 = lib.parse_graph_text(text)
                consider(n3, e3)
            except Exception:
                pass

    # Use any spare degree in the best graph to add vertices.
    if time.monotonic() < final_deadline:
        n4, e4 = _slack_extend(best[0], best[1], d, D, rng, final_deadline)
        consider(n4, e4)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
