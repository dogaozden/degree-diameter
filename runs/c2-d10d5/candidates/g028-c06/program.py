import time

import lib


# ----------------------------------------------------------------------------
# Bold change: bi-lifts over non-metacyclic groups SL(2,p) x Z_m.
#
# The parent searched bi-Cayley lifts over metacyclic groups Z_m x| Z_k. This
# version lifts a small base bipartite multigraph (K vertices per side, DEG
# layers, each layer a perfect matching with voltages) over the group
# G = SL(2,p) x Z_m, for p in {5,7,11,13}. Left multiplication by G is an
# automorphism, so the diameter test only needs the 2K base vertices. A bandit
# chooses (K, p) pairs, and simulated annealing repairs the lift.
#
# Start graph: K_{d,d}, which has diameter 2 and is always valid for D >= 2.
# The C result is accepted only if lib.is_valid passes, otherwise the
# fallback is returned.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK 3
#define NPR 4
#define NC (MAXK*NPR)

static const int PR[NPR] = {5, 7, 11, 13};

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

static int DEG, DIAM, CAP;
static double TL, tstart;
static int timed_out;
static uint8_t POP[256];

/* SL(2,p) multiplication and inverse tables; identity has index 0 */
static int SORD[NPR];
static uint16_t *SMUL[NPR];
static uint16_t *SINV[NPR];

/* current lift state */
static int PI, MZ, GS, K, G, N;
static uint8_t FULL;

static int *nbr, *lay, *vol;
static uint8_t *cur, *scr, *tmpb;
static int *bestnbr;
static int have_best, bestK, bestG, bestN;
static int have_near, nr_K, nr_PI, nr_M, nr_N;
static int64_t nr_cost, LASTCOST;
static int *nr_lay, *nr_vol;

static double elapsed(void) {
    return (double)clock() / CLOCKS_PER_SEC - tstart;
}

static int enc4(int p, int a, int b, int c, int d) {
    return ((a * p + b) * p + c) * p + d;
}

static void build_sl(int pi) {
    int p = PR[pi];
    int cells = p * p * p * p;
    int S = p * (p * p - 1);
    int *idx = malloc(sizeof(int) * (size_t)cells);
    int *A = malloc(sizeof(int) * 4 * (size_t)S);
    for (int i = 0; i < cells; i++) idx[i] = -1;
    int n = 0;
    for (int pass = 0; pass < 2; pass++)
        for (int a = 0; a < p; a++)
            for (int b = 0; b < p; b++)
                for (int c = 0; c < p; c++)
                    for (int d = 0; d < p; d++) {
                        int isid = (a == 1 && b == 0 && c == 0 && d == 1);
                        if ((pass == 0) != isid) continue;
                        int det = ((a * d - b * c) % p + p) % p;
                        if (det != 1) continue;
                        if (n >= S) continue;
                        A[4 * n] = a;
                        A[4 * n + 1] = b;
                        A[4 * n + 2] = c;
                        A[4 * n + 3] = d;
                        idx[enc4(p, a, b, c, d)] = n;
                        n++;
                    }
    SORD[pi] = S;
    SMUL[pi] = malloc(sizeof(uint16_t) * (size_t)S * (size_t)S);
    SINV[pi] = malloc(sizeof(uint16_t) * (size_t)S);
    for (int x = 0; x < S; x++) {
        int a = A[4 * x], b = A[4 * x + 1], c = A[4 * x + 2], d = A[4 * x + 3];
        for (int y = 0; y < S; y++) {
            int e = A[4 * y], f = A[4 * y + 1], g = A[4 * y + 2], h = A[4 * y + 3];
            int r0 = (a * e + b * g) % p;
            int r1 = (a * f + b * h) % p;
            int r2 = (c * e + d * g) % p;
            int r3 = (c * f + d * h) % p;
            SMUL[pi][(size_t)x * S + y] = (uint16_t)idx[enc4(p, r0, r1, r2, r3)];
        }
        int ia = d, ib = (p - b) % p, ic = (p - c) % p, id = a;
        SINV[pi][x] = (uint16_t)idx[enc4(p, ia, ib, ic, id)];
    }
    free(idx);
    free(A);
}

/* group element x = s*MZ + z with s in SL(2,p), z in Z_MZ */
static inline int gmul(int x, int y) {
    int s = x / MZ, z = x - s * MZ;
    int t = y / MZ, w = y - t * MZ;
    int s2 = SMUL[PI][(size_t)s * GS + t];
    int z2 = z + w;
    if (z2 >= MZ) z2 -= MZ;
    return s2 * MZ + z2;
}

static inline int ginv(int x) {
    int s = x / MZ, z = x - s * MZ;
    int si = SINV[PI][s];
    int zi = (MZ - z) % MZ;
    return si * MZ + zi;
}

static void set_group(int k, int pi, int m) {
    K = k;
    PI = pi;
    MZ = m;
    GS = SORD[pi];
    G = GS * m;
    N = 2 * K * G;
    FULL = (uint8_t)((1u << (2 * K)) - 1);
}

/* dart (i, p, s): A_i g ~ B_p (g s) for all g */
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
    return unreached(r) + 1000LL * dupcount();
}

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
            /* layer swap: exchange two permutation entries inside one layer */
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
            /* voltage exchange of one base vertex between two layers */
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
            /* single voltage change, defect-targeted with probability 0.4 */
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

static void save_near(void) {
    have_near = 1;
    nr_K = K;
    nr_PI = PI;
    nr_M = MZ;
    nr_N = N;
    nr_cost = LASTCOST;
    memcpy(nr_lay, lay, sizeof(int) * (size_t)DEG * MAXK);
    memcpy(nr_vol, vol, sizeof(int) * (size_t)DEG * MAXK);
}

/* choose a group size: 2*K*S*m > found and <= CAP */
static int pick_m(int k, int pi, int64_t found) {
    int64_t unit = 2LL * k * SORD[pi];
    int64_t mmin = found / unit + 1;
    int64_t mmax = (int64_t)CAP / unit;
    if (mmin < 1) mmin = 1;
    if (mmin > mmax) return 0;
    int64_t span = mmax - mmin;
    if (span > 4) span = 4;
    return (int)(mmin + rndint((int)span + 1));
}

static int pick_combo(const double *tr, const double *wn) {
    if (rnd01() < 0.2) return rndint(NC);
    int bc = 0;
    double bv = -1.0;
    for (int c = 0; c < NC; c++) {
        double v = (wn[c] + 1.0) / (tr[c] + 2.0) + 0.02 * rnd01();
        if (v > bv) {
            bv = v;
            bc = c;
        }
    }
    return bc;
}

int main(int argc, char **argv) {
    if (argc < 7) {
        fprintf(stderr, "usage: d D start cap seed time\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    long long start0 = atoll(argv[3]);
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

    if (DEG < 3 || DIAM < 3 || CAP < 8 || DEG > 200) {
        printf("0 0\n");
        return 0;
    }

    for (int pi = 0; pi < NPR; pi++) build_sl(pi);

    nbr = malloc(sizeof(int) * (size_t)DEG * CAP);
    lay = malloc(sizeof(int) * (size_t)DEG * MAXK);
    vol = malloc(sizeof(int) * (size_t)DEG * MAXK);
    nr_lay = malloc(sizeof(int) * (size_t)DEG * MAXK);
    nr_vol = malloc(sizeof(int) * (size_t)DEG * MAXK);
    cur = malloc((size_t)CAP);
    scr = malloc((size_t)CAP);
    tmpb = malloc((size_t)CAP);
    bestnbr = malloc(sizeof(int) * (size_t)DEG * CAP);
    if (!nbr || !lay || !vol || !nr_lay || !nr_vol || !cur || !scr || !tmpb || !bestnbr) {
        printf("0 0\n");
        return 0;
    }

    double tr[NC], wn[NC];
    memset(tr, 0, sizeof(tr));
    memset(wn, 0, sizeof(wn));
    long long found = start0;
    int fails = 0;

    while (elapsed() < TL) {
        if (found >= CAP) break;
        int ok = 0;
        int combo = -1;

        if (have_near && nr_N > found && rnd01() < 0.5) {
            /* iterated local search: kick the saved near miss and re-anneal */
            set_group(nr_K, nr_PI, nr_M);
            memcpy(lay, nr_lay, sizeof(int) * (size_t)DEG * MAXK);
            memcpy(vol, nr_vol, sizeof(int) * (size_t)DEG * MAXK);
            int kicks = 2 + rndint(4);
            for (int q = 0; q < kicks; q++) {
                int l = rndint(DEG), i = rndint(K);
                vol[l * K + i] = rndint(G);
            }
            ok = run_trial(3000, 1000, 0);
        } else {
            int m = 0, k = 1, pi = 0;
            for (int tries = 0; tries < 50; tries++) {
                combo = pick_combo(tr, wn);
                k = combo / NPR + 1;
                pi = combo % NPR;
                m = pick_m(k, pi, found);
                if (m) break;
            }
            if (!m) {
                fails++;
                if (fails > 200) break;
                continue;
            }
            fails = 0;
            set_group(k, pi, m);
            tr[combo] += 1.0;
            ok = run_trial(4000, 1200, 1);
        }

        /* near miss: keep annealing the same group from its final state */
        int extra = 0;
        while (!ok && !timed_out && extra < 3 && LASTCOST <= (int64_t)N / 2 && elapsed() < TL) {
            ok = run_trial(6000, 2000, 0);
            extra++;
        }

        if (!ok && !timed_out && LASTCOST > 0) {
            if (!have_near || LASTCOST < nr_cost || nr_N <= found) save_near();
        }

        if (ok) {
            if (combo >= 0) wn[combo] += 1.0;
            found = N;
            memcpy(bestnbr, nbr, sizeof(int) * (size_t)DEG * N);
            bestN = N;
            bestK = K;
            bestG = G;
            have_best = 1;
            have_near = 0;
        }
        if (timed_out) break;
    }

    if (!have_best) {
        printf("0 0\n");
        return 0;
    }
    int KG = bestK * bestG;
    printf("%d %lld\n", 2 * KG, (long long)KG * DEG);
    for (int u = 0; u < KG; u++)
        for (int l = 0; l < DEG; l++)
            printf("%d %d\n", u, bestnbr[(size_t)l * bestN + u]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact construction for the D = 3 calibration: PG(2, q) incidence graph.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Main build: exact construction for D = 3, otherwise group-lift search in C.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))

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

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if lib.is_prime_power(d - 1):
                return best

    if d >= 3 and D >= 3:
        remaining = budget - (time.monotonic() - start)
        if remaining > 2.0:
            cap = min(lib.moore_bound(d, D), 40000)
            try:
                text = lib.run_c(C_SOURCE,
                                 [d, D, best_n, cap, int(seed) & 0x7FFFFFFF, round(remaining, 2)],
                                 timeout=remaining + 20.0)
                n2, e2 = lib.parse_graph_text(text)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
