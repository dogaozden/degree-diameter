import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Two-phase program.
#
# Phase 1 (unchanged search family): bi-Cayley voltage annealing over
# Z_m x| Z_k2 in C, seeded by exact start graphs (PG(2,q), W(q)) and K_{d,d}.
#
# Phase 2 (new, different in kind): a non-lifted graph search in C that works on
# the ordinary graph, not on a group lift. It alternates
#   - double-edge swaps (degree- and bipartition-preserving), and
#   - "grow" moves: delete d edges (x_i, y_i) with distinct x_i and distinct y_i,
#     then add two new vertices w (joined to all x_i) and w' (joined to all y_i).
# Every accepted state is checked exactly by a bitset all-pairs distance test in C,
# so the search only ever moves between valid graphs and the vertex count never drops.
#
# Safety: every candidate passes lib.is_valid before it is returned. Compile errors,
# runtime errors, timeouts and malformed output are caught, and the best graph so far
# (at worst K_{d,d} or an exact construction) is returned.
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

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
}

static double elapsed(void) {
    return now_s() - tstart;
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
        double mv = rnd01();

        if (K >= 2 && mv < 0.25) {
            /* layer-swap move: exchange two permutation entries at one layer */
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
        } else if (DEG >= 2 && mv < 0.40) {
            /* voltage exchange: swap voltages of base vertex i between two layers */
            int l1 = rndint(DEG);
            int l2 = rndint(DEG - 1);
            if (l2 >= l1) l2++;
            int i = rndint(K);
            int e1 = l1 * K + i, e2 = l2 * K + i;
            int v1 = vol[e1], v2 = vol[e2];
            if (v1 == v2) continue;
            vol[e1] = v2;
            vol[e2] = v1;
            set_dart(l1, i, lay[e1], v2);
            set_dart(l2, i, lay[e2], v1);
            compute_reach(scr);
            c2 = total_cost(scr);
            if (!(c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp))) {
                vol[e1] = v1;
                vol[e2] = v2;
                set_dart(l1, i, lay[e1], v1);
                set_dart(l2, i, lay[e2], v2);
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
    tstart = now_s();

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


EXT_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXDEG 64
#define MAXNIN 12000

static uint64_t rs;
static uint64_t rnd64(void) {
    uint64_t x = rs;
    x ^= x >> 12;
    x ^= x << 25;
    x ^= x >> 27;
    rs = x;
    return x * 2685821657736338717ULL;
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
}

static int DEG, DIAM;
static int n, m, capV, capE;
static int *deg, *adj, *side;
static int *ea, *eb;             /* edge e: ea on side 0, eb on side 1 */
static uint64_t *bufA, *bufB;
static int *bdeg, *badj, *bside, *bea, *beb;
static int bn, bm;

static int has_edge(int a, int b) {
    int base = a * DEG;
    for (int k = 0; k < deg[a]; k++)
        if (adj[base + k] == b) return 1;
    return 0;
}

static void adj_remove(int v, int w) {
    int base = v * DEG;
    for (int k = 0; k < deg[v]; k++) {
        if (adj[base + k] == w) {
            adj[base + k] = adj[base + deg[v] - 1];
            deg[v]--;
            return;
        }
    }
}

static void adj_add(int v, int w) {
    adj[v * DEG + deg[v]] = w;
    deg[v]++;
}

static void edge_remove_idx(int e) {
    m--;
    ea[e] = ea[m];
    eb[e] = eb[m];
}

/* Exact check: every pair of vertices within distance DIAM. Bitset BFS. */
static int check_valid(void) {
    int W = (n + 63) >> 6;
    uint64_t *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int t = 0; t < DIAM; t++) {
        int changed = 0;
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * (size_t)W);
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *s2 = cur + (size_t)adj[v * DEG + k] * W;
                for (int w = 0; w < W; w++) dst[w] |= s2[w];
            }
            for (int w = 0; w < W; w++)
                if (dst[w] != src[w]) changed = 1;
        }
        uint64_t *tmp = cur;
        cur = nxt;
        nxt = tmp;
        if (!changed) break;
    }
    int bits = n - 64 * (W - 1);
    uint64_t lastmask = (bits >= 64) ? ~0ULL : ((1ULL << bits) - 1);
    for (int v = 0; v < n; v++) {
        const uint64_t *r = cur + (size_t)v * W;
        for (int w = 0; w < W - 1; w++)
            if (r[w] != ~0ULL) return 0;
        if ((r[W - 1] & lastmask) != lastmask) return 0;
    }
    return 1;
}

static void save_backup(void) {
    bn = n;
    bm = m;
    memcpy(bdeg, deg, sizeof(int) * (size_t)capV);
    memcpy(badj, adj, sizeof(int) * (size_t)capV * DEG);
    memcpy(bside, side, sizeof(int) * (size_t)capV);
    memcpy(bea, ea, sizeof(int) * (size_t)capE);
    memcpy(beb, eb, sizeof(int) * (size_t)capE);
}

static void restore_backup(void) {
    n = bn;
    m = bm;
    memcpy(deg, bdeg, sizeof(int) * (size_t)capV);
    memcpy(adj, badj, sizeof(int) * (size_t)capV * DEG);
    memcpy(side, bside, sizeof(int) * (size_t)capV);
    memcpy(ea, bea, sizeof(int) * (size_t)capE);
    memcpy(eb, beb, sizeof(int) * (size_t)capE);
}

/* Double-edge swap: (a,b),(c,e) -> (a,e),(c,b), with a,c on side 0 and b,e on side 1. */
static int move_swap(void) {
    if (m < 2) return 0;
    for (int tries = 0; tries < 50; tries++) {
        int e1 = rndint(m), e2 = rndint(m);
        if (e1 == e2) continue;
        int a = ea[e1], b = eb[e1], c = ea[e2], f = eb[e2];
        if (a == c || b == f) continue;
        if (has_edge(a, f) || has_edge(c, b)) continue;
        adj_remove(a, b);
        adj_remove(b, a);
        adj_remove(c, f);
        adj_remove(f, c);
        adj_add(a, f);
        adj_add(f, a);
        adj_add(c, b);
        adj_add(b, c);
        ea[e1] = a;
        eb[e1] = f;
        ea[e2] = c;
        eb[e2] = b;
        return 1;
    }
    return 0;
}

/* Grow: remove DEG edges with distinct endpoints on both sides, then add
   w (side 1) joined to the DEG side-0 endpoints and w2 (side 0) joined to the
   DEG side-1 endpoints. Net: +2 vertices, +DEG edges. */
static int move_grow(void) {
    if (n + 2 > capV || m < DEG) return 0;
    int idx[MAXDEG], xs[MAXDEG], ys[MAXDEG];
    int cnt = 0;
    for (int tries = 0; tries < 300 && cnt < DEG; tries++) {
        int e = rndint(m);
        int ok = 1;
        for (int j = 0; j < cnt && ok; j++)
            if (idx[j] == e || ea[idx[j]] == ea[e] || eb[idx[j]] == eb[e]) ok = 0;
        if (ok) idx[cnt++] = e;
    }
    if (cnt < DEG) return 0;
    for (int j = 0; j < cnt; j++) {
        xs[j] = ea[idx[j]];
        ys[j] = eb[idx[j]];
    }
    for (int j = 0; j < cnt; j++) {
        adj_remove(xs[j], ys[j]);
        adj_remove(ys[j], xs[j]);
    }
    /* sort indices in descending order for swap-removal */
    for (int i = 1; i < cnt; i++) {
        int t = idx[i], j = i - 1;
        while (j >= 0 && idx[j] < t) {
            idx[j + 1] = idx[j];
            j--;
        }
        idx[j + 1] = t;
    }
    for (int j = 0; j < cnt; j++) edge_remove_idx(idx[j]);

    int w = n, w2 = n + 1;
    side[w] = 1;
    side[w2] = 0;
    deg[w] = 0;
    deg[w2] = 0;
    for (int j = 0; j < cnt; j++) {
        adj_add(xs[j], w);
        adj_add(w, xs[j]);
        adj_add(ys[j], w2);
        adj_add(w2, ys[j]);
        ea[m] = xs[j];
        eb[m] = w;
        m++;
        ea[m] = w2;
        eb[m] = ys[j];
        m++;
    }
    n += 2;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: d D seed time\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double TLIM = atof(argv[4]);
    double t0 = now_s();

    rs = (seed + 1) * 0xA0761D6478BD642FULL ^ 0xE7037ED1A0B428DBULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();

    int nin = 0, min_ = 0;
    if (scanf("%d %d", &nin, &min_) != 2) {
        printf("0 0\n");
        return 0;
    }
    if (nin < 2 || nin > MAXNIN || min_ < 1 || DEG < 1 || DEG > MAXDEG || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    int *eu = malloc(sizeof(int) * (size_t)min_);
    int *ev = malloc(sizeof(int) * (size_t)min_);
    if (!eu || !ev) {
        printf("0 0\n");
        return 0;
    }
    for (int i = 0; i < min_; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= nin || v >= nin || u == v) {
            printf("0 0\n");
            return 0;
        }
        eu[i] = u;
        ev[i] = v;
    }

    capV = nin + 1024;
    capE = capV * DEG;
    int wcap = (capV + 63) >> 6;
    deg = calloc((size_t)capV, sizeof(int));
    adj = calloc((size_t)capE, sizeof(int));
    side = calloc((size_t)capV, sizeof(int));
    ea = calloc((size_t)capE, sizeof(int));
    eb = calloc((size_t)capE, sizeof(int));
    bdeg = calloc((size_t)capV, sizeof(int));
    badj = calloc((size_t)capE, sizeof(int));
    bside = calloc((size_t)capV, sizeof(int));
    bea = calloc((size_t)capE, sizeof(int));
    beb = calloc((size_t)capE, sizeof(int));
    bufA = malloc(sizeof(uint64_t) * (size_t)capV * wcap);
    bufB = malloc(sizeof(uint64_t) * (size_t)capV * wcap);
    int *queue = malloc(sizeof(int) * (size_t)capV);
    if (!deg || !adj || !side || !ea || !eb || !bdeg || !badj || !bside || !bea || !beb ||
        !bufA || !bufB || !queue) {
        printf("0 0\n");
        return 0;
    }

    n = nin;
    m = 0;
    for (int i = 0; i < min_; i++) {
        int u = eu[i], v = ev[i];
        if (deg[u] >= DEG || deg[v] >= DEG || has_edge(u, v)) {
            printf("0 0\n");
            return 0;
        }
        adj_add(u, v);
        adj_add(v, u);
    }

    /* bipartition */
    for (int v = 0; v < n; v++) side[v] = -1;
    for (int s = 0; s < n; s++) {
        if (side[s] != -1) continue;
        side[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int u = queue[qh++];
            for (int k = 0; k < deg[u]; k++) {
                int w = adj[u * DEG + k];
                if (side[w] == -1) {
                    side[w] = 1 - side[u];
                    queue[qt++] = w;
                } else if (side[w] == side[u]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }

    /* orient edges: ea on side 0, eb on side 1 */
    for (int i = 0; i < min_; i++) {
        int u = eu[i], v = ev[i];
        if (side[u] == 0) {
            ea[m] = u;
            eb[m] = v;
        } else {
            ea[m] = v;
            eb[m] = u;
        }
        m++;
    }

    if (!check_valid()) {
        printf("0 0\n");
        return 0;
    }

    while (now_s() - t0 < TLIM) {
        save_backup();
        int grow = rnd01() < 0.3;
        int applied = grow ? move_grow() : move_swap();
        if (!applied) continue;
        if (!check_valid()) restore_backup();
    }

    printf("%d %d\n", n, m);
    for (int e = 0; e < m; e++) printf("%d %d\n", ea[e], eb[e]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact constructions used as start graphs.
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
# Main build: exact constructions, then the C voltage-lift search (first part of
# the budget), then the C graph-level grow/swap search on the best graph so far.
# ----------------------------------------------------------------------------

_MAX_CAP = 2_000_000  # keeps the C allocations and the int parsing safe


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    final_deadline = start + max(1.0, time_limit - 3.0)

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

    # Exact constructions: return immediately on calibration-style cases.
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

    if d < 3 or D < 3:
        return best

    # Phase 1: voltage-lift search in C, for the first half of the budget.
    lift_deadline = start + 0.5 * budget
    remaining = lift_deadline - time.monotonic()
    if remaining > 2.0:
        cap = min(lib.moore_bound(d, D), _MAX_CAP)
        if cap > best_n:
            try:
                text = lib.run_c(C_SOURCE,
                                 [d, D, best_n, cap, int(seed) & 0x7FFFFFFF, round(remaining, 2)],
                                 timeout=remaining + 20.0)
                n2, e2 = lib.parse_graph_text(text)
                consider(n2, e2)
            except Exception:
                pass

    # Phase 2: graph-level grow/swap search in C, starting from the best graph so far.
    ext_time = final_deadline - 2.0 - time.monotonic()
    if ext_time > 2.0:
        try:
            text = lib.run_c(EXT_SOURCE,
                             [d, D, int(seed) & 0x7FFFFFFF, round(ext_time, 2)],
                             stdin_graph=best,
                             timeout=ext_time + 15.0)
            n2, e2 = lib.parse_graph_text(text)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
