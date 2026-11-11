import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Two-stage search for the weakest targets.
#
# Stage 1 (volt): the bi-Cayley voltage annealing engine from the parent, which
#   builds a lift over Z_m x| Z_k2 and returns a valid graph larger than the start.
# Stage 2 (ins): a different construction. Starting from the stage-1 graph (or
#   K_{d,d}), it inserts vertex pairs by splitting a matching of d edges, which
#   keeps every degree at d and the graph bipartite. It then repairs the new
#   bad pairs with degree-preserving 2-switches, annealing on the number of
#   unordered pairs at distance > D. Only states with zero bad pairs are kept.
#
# Every returned graph is checked with lib.is_valid. K_{d,d} is the fallback.
# ----------------------------------------------------------------------------

C_VOLT = r"""
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


C_INS = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXDEG 256

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

/* Bipartite DEG-regular graph: A vertices 0..H-1, B vertices 0..H-1 (vertex id H+b).
   Edge e joins A index EA[e] and B index EB[e]. M = H*DEG edges. */
static int DEG, DIAM, CAPH, H, M, W;
static int *EA, *EB;
static int *NA, *NAE, *NB, *NBE;      /* slot tables for A and B vertices */
static int *cntA, *cntB, *markA, *markB;
static int *badv, *cbad, nbad, ncbad;
static uint64_t *RC, *RT;
static int gen = 0;
static double TL, tstart;

static double elapsed(void) {
    return (double)clock() / CLOCKS_PER_SEC - tstart;
}

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int build_adj(void) {
    for (int i = 0; i < H; i++) {
        cntA[i] = 0;
        cntB[i] = 0;
    }
    for (int e = 0; e < M; e++) {
        int a = EA[e], b = EB[e];
        if (a < 0 || a >= H || b < 0 || b >= H) return 0;
        if (cntA[a] >= DEG || cntB[b] >= DEG) return 0;
        NA[a * DEG + cntA[a]] = b;
        NAE[a * DEG + cntA[a]] = e;
        cntA[a]++;
        NB[b * DEG + cntB[b]] = a;
        NBE[b * DEG + cntB[b]] = e;
        cntB[b]++;
    }
    for (int i = 0; i < H; i++)
        if (cntA[i] != DEG || cntB[i] != DEG) return 0;
    return 1;
}

static int isedge(int a, int b) {
    for (int k = 0; k < DEG; k++)
        if (NA[a * DEG + k] == b) return 1;
    return 0;
}

/* Returns the number of unordered pairs at distance > DIAM. Fills badv/nbad. */
static int64_t evaluate(void) {
    int N = 2 * H;
    W = (N + 63) >> 6;
    size_t sz = (size_t)N * W;
    memset(RC, 0, sizeof(uint64_t) * sz);
    for (int v = 0; v < N; v++) RC[(size_t)v * W + (v >> 6)] = 1ULL << (v & 63);
    for (int t = 0; t < DIAM; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint64_t *dst = RT + (size_t)v * W;
            const uint64_t *src = RC + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * W);
            for (int k = 0; k < DEG; k++) {
                int u = (v < H) ? H + NA[v * DEG + k] : NB[(v - H) * DEG + k];
                const uint64_t *s2 = RC + (size_t)u * W;
                for (int w = 0; w < W; w++) dst[w] |= s2[w];
            }
            for (int w = 0; w < W; w++)
                if (dst[w] != src[w]) {
                    changed = 1;
                    break;
                }
        }
        uint64_t *tmp = RC;
        RC = RT;
        RT = tmp;
        if (!changed) break;
    }
    int64_t un = 0;
    nbad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        const uint64_t *src = RC + (size_t)v * W;
        for (int w = 0; w < W; w++) c += popc64(src[w]);
        int miss = N - c;
        if (miss > 0) {
            un += miss;
            badv[nbad++] = v;
        }
    }
    return un / 2;
}

/* Degree-preserving 2-switch annealing. Returns 1 if a valid state (cost 0) is reached.
   On return 0 the state may be invalid; the caller restores a snapshot. */
static int anneal(int maxit) {
    if (!build_adj()) return 0;
    int64_t cost = evaluate();
    if (cost == 0) return 1;
    memcpy(cbad, badv, sizeof(int) * nbad);
    ncbad = nbad;
    double T0 = 1.0 + 0.05 * (double)cost;
    for (int it = 0; it < maxit; it++) {
        if ((it & 15) == 0 && elapsed() > TL) return 0;
        double frac = (double)it / (double)maxit;
        double T = 0.25 + (T0 - 0.25) * (1.0 - frac);
        int e1, e2;
        if (ncbad > 0 && rnd01() < 0.7) {
            int u = cbad[rndint(ncbad)];
            int slot = rndint(DEG);
            e1 = (u < H) ? NAE[u * DEG + slot] : NBE[(u - H) * DEG + slot];
        } else {
            e1 = rndint(M);
        }
        e2 = rndint(M);
        if (e1 == e2) continue;
        int a1 = EA[e1], b1 = EB[e1], a2 = EA[e2], b2 = EB[e2];
        if (a1 == a2 || b1 == b2) continue;
        if (isedge(a1, b2) || isedge(a2, b1)) continue;
        EB[e1] = b2;
        EB[e2] = b1;
        if (!build_adj()) return 0;
        int64_t c2 = evaluate();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
            memcpy(cbad, badv, sizeof(int) * nbad);
            ncbad = nbad;
            if (cost == 0) return 1;
        } else {
            EB[e1] = b1;
            EB[e2] = b2;
            if (!build_adj()) return 0;
        }
    }
    return 0;
}

/* Insert s vertex pairs. Each pair takes a matching of DEG edges (x_i, y_i),
   replaces them by (h, y_i), and appends (x_i, h). Degrees and bipartiteness are kept. */
static int insert_pairs(int s) {
    for (int p = 0; p < s; p++) {
        if (H + 1 > CAPH) return 0;
        int pos[MAXDEG], xs[MAXDEG], ys[MAXDEG];
        int ok = 0;
        for (int att = 0; att < 200 && !ok; att++) {
            gen++;
            int cnt = 0;
            for (int t = 0; t < 50 * DEG && cnt < DEG; t++) {
                int e = rndint(M);
                int a = EA[e], b = EB[e];
                if (markA[a] == gen || markB[b] == gen) continue;
                markA[a] = gen;
                markB[b] = gen;
                pos[cnt] = e;
                xs[cnt] = a;
                ys[cnt] = b;
                cnt++;
            }
            if (cnt == DEG) ok = 1;
        }
        if (!ok) return 0;
        int h = H;
        for (int i = 0; i < DEG; i++) EA[pos[i]] = h;
        for (int i = 0; i < DEG; i++) {
            EA[M] = xs[i];
            EB[M] = h;
            M++;
        }
        H++;
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        printf("0 0\n");
        return 0;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    long long cap = atoll(argv[3]);
    unsigned long long seed = strtoull(argv[4], NULL, 10);
    TL = atof(argv[5]);
    tstart = (double)clock() / CLOCKS_PER_SEC;

    rs = (seed + 7) * 0x9E3779B97F4A7C15ULL ^ 0xA5A5A5A5DEADBEEFULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();

    if (DEG < 2 || DEG > MAXDEG || DIAM < 2 || cap < 2 * DEG) {
        printf("0 0\n");
        return 0;
    }

    CAPH = (int)(cap / 2) + 4;
    int Nmax = 2 * CAPH;
    int Wmax = (Nmax + 63) >> 6;
    EA = calloc((size_t)CAPH * DEG + DEG, sizeof(int));
    EB = calloc((size_t)CAPH * DEG + DEG, sizeof(int));
    NA = calloc((size_t)CAPH * DEG, sizeof(int));
    NAE = calloc((size_t)CAPH * DEG, sizeof(int));
    NB = calloc((size_t)CAPH * DEG, sizeof(int));
    NBE = calloc((size_t)CAPH * DEG, sizeof(int));
    cntA = calloc((size_t)CAPH, sizeof(int));
    cntB = calloc((size_t)CAPH, sizeof(int));
    markA = calloc((size_t)CAPH, sizeof(int));
    markB = calloc((size_t)CAPH, sizeof(int));
    badv = calloc((size_t)Nmax, sizeof(int));
    cbad = calloc((size_t)Nmax, sizeof(int));
    RC = calloc((size_t)Nmax * Wmax, sizeof(uint64_t));
    RT = calloc((size_t)Nmax * Wmax, sizeof(uint64_t));
    int *sA = calloc((size_t)CAPH * DEG + DEG, sizeof(int));
    int *sB = calloc((size_t)CAPH * DEG + DEG, sizeof(int));
    if (!EA || !EB || !NA || !NAE || !NB || !NBE || !cntA || !cntB || !markA || !markB ||
        !badv || !cbad || !RC || !RT || !sA || !sB) {
        printf("0 0\n");
        return 0;
    }

    /* Start: the given DEG-regular bipartite graph (lines "n m", then edges u v with
       A vertices 0..n/2-1 and B vertices n/2..n-1), or K_{d,d} if none is valid. */
    int have = 0;
    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) == 2 && n0 > 0 && m0 > 0 && n0 % 2 == 0 &&
        n0 / 2 <= CAPH && m0 == (n0 / 2) * DEG) {
        int hh = n0 / 2;
        int good = 1;
        for (int i = 0; i < m0 && good; i++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) {
                good = 0;
                break;
            }
            if (u > v) {
                int t = u;
                u = v;
                v = t;
            }
            if (u < 0 || u >= hh || v < hh || v >= n0) {
                good = 0;
            } else {
                EA[i] = u;
                EB[i] = v - hh;
            }
        }
        if (good) {
            H = hh;
            M = m0;
            have = 1;
        }
    }
    if (have) {
        if (!build_adj()) have = 0;
        else if (evaluate() != 0) have = 0;
    }
    if (!have) {
        H = DEG;
        M = DEG * DEG;
        for (int i = 0; i < DEG; i++)
            for (int j = 0; j < DEG; j++) {
                EA[i * DEG + j] = i;
                EB[i * DEG + j] = j;
            }
        if (!build_adj()) {
            printf("0 0\n");
            return 0;
        }
        evaluate();
    }

    int step = H / 50;
    if (step < 1) step = 1;
    int fails = 0;
    while (elapsed() < TL && fails < 8) {
        int sH = H, sM = M;
        memcpy(sA, EA, sizeof(int) * (size_t)M);
        memcpy(sB, EB, sizeof(int) * (size_t)M);
        int ok = 0;
        if (insert_pairs(step)) {
            int maxit = 200 + H / 4;
            ok = anneal(maxit);
        }
        if (ok) {
            fails = 0;
            step = step + step / 2 + 1;
            if (step > H / 20 + 1) step = H / 20 + 1;
        } else {
            H = sH;
            M = sM;
            memcpy(EA, sA, sizeof(int) * (size_t)M);
            memcpy(EB, sB, sizeof(int) * (size_t)M);
            fails++;
            step /= 2;
            if (step < 1) step = 1;
        }
    }

    /* The current state is always valid here (cost 0). */
    int N = 2 * H;
    printf("%d %d\n", N, M);
    for (int e = 0; e < M; e++) printf("%d %d\n", EA[e], H + EB[e]);
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


def _ab_form(n, edges):
    """Relabel a bipartite graph so A vertices are 0..h-1 and B vertices are h..2h-1.

    Returns (2h, edges) with every edge written as (A, B), or None if the graph is not
    bipartite with equal sides.
    """
    adj = lib.adjacency(n, edges)
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
    A = [v for v in range(n) if color[v] == 0]
    B = [v for v in range(n) if color[v] == 1]
    if not A or len(A) != len(B):
        return None
    idx = {}
    for i, v in enumerate(A):
        idx[v] = i
    for i, v in enumerate(B):
        idx[v] = i
    h = len(A)
    out = []
    for u, v in edges:
        if color[u] == 1:
            u, v = v, u
        out.append((idx[u], h + idx[v]))
    return 2 * h, out


# ----------------------------------------------------------------------------
# Main build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.9 * time_limit, time_limit - 5.0))
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

    # Exact constructions: return immediately on the calibration-style cases.
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

    if d >= 3 and D >= 3:
        cap = lib.moore_bound(d, D)
        seed_arg = int(seed) & 0x7FFFFFFF

        # Stage 1: voltage-lift annealing (parent engine), about half the budget.
        remaining = deadline - time.monotonic()
        if remaining > 2.0:
            t1 = remaining * 0.5
            try:
                text = lib.run_c(C_VOLT,
                                 [d, D, best_n, cap, seed_arg, round(t1, 2)],
                                 timeout=t1 + 20.0)
                consider(*lib.parse_graph_text(text))
            except Exception:
                pass

        # Stage 2: vertex-pair insertion with 2-switch repair, from the best graph so far.
        remaining = deadline - time.monotonic()
        if remaining > 2.0 and d >= 3:
            start_graph = None
            if best_n > 2 * d:
                start_graph = _ab_form(best[0], best[1])
            try:
                text = lib.run_c(C_INS,
                                 [d, D, cap, seed_arg, round(remaining - 1.0, 2)],
                                 stdin_graph=start_graph,
                                 timeout=remaining + 20.0)
                consider(*lib.parse_graph_text(text))
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
