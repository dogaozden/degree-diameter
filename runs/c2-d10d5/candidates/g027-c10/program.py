import time

import lib


# ----------------------------------------------------------------------------
# Bi-Cayley voltage search with wider base graphs.
#
# A lift over a group G = Z_m x| Z_k2 with K base vertices per side, so a
# candidate has N = 2*K*|G| vertices. Each block is a permutation layer for
# every degree slot, which keeps the graph DEG-regular and bipartite.
#
# Changes from the previous engine:
#   - base size K up to 8 (block reach masks are uint16 instead of uint8),
#     so the search can use much larger lifts;
#   - a single annealing run per sampled group, with defect-targeted voltage
#     moves and layer / voltage exchange moves;
#   - a shorter wall-clock budget and a smaller cap, so memory stays bounded.
#
# Safe fallback: K_{d,d}, PG(2,q) and Araujo-Lopez graphs, all checked with
# lib.is_valid. Only a candidate that passes lib.is_valid replaces the fallback.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define KMAX 8
#define NCH 20
#define PEN 1000

typedef uint16_t mask_t;

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

static const int K2C[NCH] = {1,1,2,2,3,4,5,6,7,8,9,10,12,14,16,18,20,24,30,36};

static int DEG, DIAM, CAP;
static int K, K2, M, R, G, N;
static int64_t PWR[64];
static int *AA, *BB;
static int *nbr;        /* nbr[l*N + v] */
static int *lay, *vol; /* index l*KMAX + i */
static mask_t *cur, *scr, *tmpm;
static uint8_t POP[65536];
static mask_t FULL;
static int timed_out;
static double tstart, TL;
static int64_t LASTCOST;
static int have_best;
static int bestK, bestG, bestN;
static int *bestnbr;

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
    if (b < 0) b += m;
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
    for (int at = 0; at < 200; at++) {
        int k2 = K2C[rndint(NCH)];
        int64_t m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        int64_t r = -1;
        if (k2 == 1) {
            r = 1;
        } else if (k2 == 2 && rnd01() < 0.3) {
            r = m - 1;
            if (powmod(r, 2, m) != 1 % m) continue;
        } else {
            for (int t = 0; t < 60; t++) {
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

/* dart (layer l, base i, base p, voltage s): A(i,x) -- B(p, x*s) */
static void set_dart(int l, int i, int p, int s) {
    int is = ginv(s);
    int *row = nbr + (size_t)l * N;
    int Ab = i * G, Bb = (K + p) * G;
    for (int g = 0; g < G; g++) {
        row[Ab + g] = Bb + gmul(g, s);
        row[Bb + g] = Ab + gmul(g, is);
    }
}

static void apply_all(void) {
    for (int l = 0; l < DEG; l++)
        for (int i = 0; i < K; i++)
            set_dart(l, i, lay[l * KMAX + i], vol[l * KMAX + i]);
}

static void init_layers(void) {
    for (int l = 0; l < DEG; l++) {
        int perm[KMAX];
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i];
            perm[i] = perm[j];
            perm[j] = t;
        }
        for (int i = 0; i < K; i++) lay[l * KMAX + i] = perm[i];
    }
    for (int l = 0; l < DEG; l++)
        for (int i = 0; i < K; i++) vol[l * KMAX + i] = rndint(G);
}

/* For each A-vertex in the base, count per-layer duplicate darts. */
static void compute_reach(mask_t *out) {
    memset(out, 0, sizeof(mask_t) * (size_t)N);
    for (int b = 0; b < 2 * K; b++) out[b * G] = (mask_t)(1u << b);
    for (int t = 0; t < DIAM; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            mask_t x = out[v];
            for (int l = 0; l < DEG; l++) x |= out[nbr[(size_t)l * N + v]];
            tmpm[v] = x;
            if (x != out[v]) changed = 1;
        }
        if (!changed) break;
        memcpy(out, tmpm, sizeof(mask_t) * (size_t)N);
    }
}

static int64_t unreached(const mask_t *r) {
    int64_t s = 0;
    for (int v = 0; v < N; v++) s += POP[r[v]];
    return (int64_t)2 * K * N - s;
}

static int dupcount(void) {
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l2 = 0; l2 < DEG; l2++)
            for (int l1 = 0; l1 < l2; l1++) {
                if (lay[l1 * KMAX + i] == lay[l2 * KMAX + i] &&
                    vol[l1 * KMAX + i] == vol[l2 * KMAX + i]) {
                    dup++;
                    break;
                }
            }
    return dup;
}

static int64_t total_cost(const mask_t *r) {
    return unreached(r) + (int64_t)PEN * dupcount();
}

static int run_anneal(int iters, int patience) {
    timed_out = 0;
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
        double mv = rnd01();
        int64_t c2 = 0;

        if (K >= 2 && mv < 0.2) {
            /* layer move: swap two entries of one permutation layer */
            int l = rndint(DEG);
            int i1 = rndint(K);
            int i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int e1 = l * KMAX + i1, e2 = l * KMAX + i2;
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
        } else if (mv < 0.35) {
            /* voltage exchange: same base vertex, two layers */
            int l1 = rndint(DEG);
            int l2 = rndint(DEG - 1);
            if (l2 >= l1) l2++;
            int i = rndint(K);
            int e1 = l1 * KMAX + i, e2 = l2 * KMAX + i;
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
            /* voltage change, targeted at an unreached vertex half the time */
            int l = rndint(DEG);
            int i = rndint(K);
            if (rnd01() < 0.5) {
                int cnt = 0, u = -1;
                for (int v = 0; v < N; v++) {
                    if (cur[v] != FULL) {
                        cnt++;
                        if (rndint(cnt) == 0) u = v;
                    }
                }
                if (u >= 0) {
                    int blk = u / G;
                    if (blk < K) {
                        i = blk;
                    } else {
                        int p = blk - K, fj = -1;
                        for (int j = 0; j < K; j++)
                            if (lay[l * KMAX + j] == p) {
                                fj = j;
                                break;
                            }
                        if (fj < 0) continue;
                        i = fj;
                    }
                }
            }
            int e = l * KMAX + i;
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
        mask_t *tb = cur;
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
    if (rnd01() < 0.2) return 1 + rndint(KMAX);
    int bk = 1;
    double bv = -1.0;
    for (int k = 1; k <= KMAX; k++) {
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
    for (int x = 0; x < 65536; x++) {
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
    lay = malloc(sizeof(int) * (size_t)DEG * KMAX);
    vol = malloc(sizeof(int) * (size_t)DEG * KMAX);
    cur = malloc(sizeof(mask_t) * (size_t)CAP);
    scr = malloc(sizeof(mask_t) * (size_t)CAP);
    tmpm = malloc(sizeof(mask_t) * (size_t)CAP);
    bestnbr = malloc(sizeof(int) * (size_t)DEG * CAP);
    if (!AA || !BB || !nbr || !lay || !vol || !cur || !scr || !tmpm || !bestnbr) {
        printf("0 0\n");
        return 0;
    }

    long long found = best0;
    double tr[KMAX + 1] = {0}, wn[KMAX + 1] = {0};

    while (elapsed() < TL) {
        if (found >= CAP) break;
        int k = pick_k(tr, wn);
        int64_t base = found / (2 * k);
        int64_t span = base / 10 + 2;
        int64_t target = base + 1 + rndint((int)span);
        if (target < 2) target = 2;
        if (!sample_group(target)) continue;
        long long Nn = 2LL * k * G;
        if (Nn <= found || Nn > CAP) continue;

        K = k;
        N = (int)Nn;
        FULL = (mask_t)((1u << (2 * K)) - 1);
        setup_group();
        tr[k] += 1.0;
        init_layers();
        apply_all();

        int ok = run_anneal(3000, 1000);
        int extra = 0;
        while (!ok && !timed_out && extra < 3 && LASTCOST <= (int64_t)N / 2 && elapsed() < TL) {
            ok = run_anneal(5000, 1500);
            extra++;
        }

        if (ok) {
            wn[k] += 1.0;
            found = N;
            bestK = K;
            bestG = G;
            bestN = N;
            memcpy(bestnbr, nbr, sizeof(int) * (size_t)DEG * N);
            have_best = 1;
        }
        if (timed_out) break;
    }

    if (!have_best) {
        printf("0 0\n");
        return 0;
    }
    int KG = bestK * bestG;
    long long m = (long long)KG * DEG;
    printf("%d %lld\n", bestN, m);
    for (int u = 0; u < KG; u++)
        for (int l = 0; l < DEG; l++)
            printf("%d %d\n", u, bestnbr[(size_t)l * bestN + u]);
    return 0;
}
"""


_MAX_CAP = 200_000  # keeps C memory and the is_valid check bounded


def _pg_graph(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (diameter 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(g):
        nonlocal best
        if g is None:
            return
        n, e = g
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        try:
            consider(_pg_graph(d))
        except Exception:
            pass
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

    # Main search in C, starting from the best exact graph.
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    if d >= 3 and D >= 3:
        remaining = start + budget - time.monotonic()
        if remaining > 2.0:
            cap = min(lib.moore_bound(d, D), _MAX_CAP)
            if cap > best[0]:
                try:
                    text = lib.run_c(
                        C_SOURCE,
                        [d, D, best[0], cap, int(seed) & 0x7FFFFFFF, round(remaining, 2)],
                        timeout=remaining + 5.0,
                    )
                    consider(lib.parse_graph_text(text))
                except Exception:
                    pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
