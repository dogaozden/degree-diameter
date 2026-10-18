import itertools
import time

import lib


# ----------------------------------------------------------------------------
# New search: bi-Cayley (Cayley-type) bipartite graphs over small semidirect
# products Z_m x| Z_k. Vertices are A_g and B_g for g in G, with A_g adjacent
# to B_{g s} for the DEG distinct connection elements s in S. Left
# multiplication is an automorphism that is transitive on each side, so the
# diameter condition reduces to two BFS runs (from A_e and from B_e). Each
# move changes one connection element, and simulated annealing minimises the
# number of vertex pairs left out of range.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 40
#define MAXG 4096
#define MAXV (2 * MAXG)

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

static int DEG, DIAM, GMAXN;
static int GM, GK, G;
static int64_t RR;
static int64_t PW[MAXG];
static int AAv[MAXG], BBv[MAXG], INV[MAXG];
static int S[MAXD];
static int NBA[MAXG * MAXD];   /* A vertex g, generator i -> B index */
static int NBB[MAXG * MAXD];   /* B vertex h, generator i -> A index */
static int dist[MAXV];
static int queue_[MAXV];
static int timed_out;
static double tstart, TL;

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

/* element (a,b) coded as a*GK+b; (a,b)(c,e) = (a + r^b c, b + e) */
static int gmul(int x, int y) {
    int64_t a2 = (AAv[x] + PW[BBv[x]] * (int64_t)AAv[y]) % GM;
    int b2 = (BBv[x] + BBv[y]) % GK;
    return (int)(a2 * GK + b2);
}

static int ginv_idx(int x) {
    int a = AAv[x], b = BBv[x];
    int nb = (GK - b) % GK;
    int64_t a2 = (GM - (PW[nb] * a) % GM) % GM;
    return (int)(a2 * GK + nb);
}

static void setup_group(int m, int k, int64_t r) {
    GM = m;
    GK = k;
    G = m * k;
    RR = r;
    PW[0] = 1 % m;
    for (int b = 1; b < k; b++) PW[b] = PW[b - 1] * r % m;
    for (int x = 0; x < G; x++) {
        AAv[x] = x / k;
        BBv[x] = x % k;
    }
    for (int x = 0; x < G; x++) INV[x] = ginv_idx(x);
}

static const int KCH[11] = {1, 1, 2, 2, 3, 4, 5, 6, 8, 10, 12};

static int sample_group(int Gt) {
    for (int at = 0; at < 100; at++) {
        int k = KCH[rndint(11)];
        int64_t m = (Gt + k - 1) / k;
        if (m < 2) m = 2;
        if (m * k < DEG) m = (DEG + k - 1) / k;
        if (k == 1) {
            setup_group((int)m, 1, 1);
            return 1;
        }
        for (int tr = 0; tr < 200; tr++) {
            int64_t r = 1 + rndint((int)(m - 1));
            if (gcd64(r, m) == 1 && powmod(r, k, m) == 1 % m) {
                setup_group((int)m, k, r);
                return 1;
            }
        }
    }
    setup_group(DEG > 2 ? DEG : 2, 1, 1);
    return 1;
}

static void setcol(int i) {
    int s = S[i], si = INV[s];
    for (int g = 0; g < G; g++) {
        NBA[g * DEG + i] = G + gmul(g, s);
        NBB[g * DEG + i] = gmul(g, si);
    }
}

static void bfs_from(int src, int *tot, int *cntB) {
    int V = 2 * G;
    for (int v = 0; v < V; v++) dist[v] = -1;
    int head = 0, tail = 0;
    queue_[tail++] = src;
    dist[src] = 0;
    while (head < tail) {
        int v = queue_[head++];
        int dv = dist[v];
        if (dv >= DIAM) continue;
        const int *row;
        if (v < G) row = &NBA[v * DEG];
        else row = &NBB[(v - G) * DEG];
        for (int i = 0; i < DEG; i++) {
            int u = row[i];
            if (dist[u] < 0) {
                dist[u] = dv + 1;
                queue_[tail++] = u;
            }
        }
    }
    int cb = 0;
    for (int q = 0; q < tail; q++)
        if (queue_[q] >= G) cb++;
    *tot = tail;
    *cntB = cb;
}

/* Pairs out of range: from A_e to all vertices, plus from B_e to all B vertices. */
static int64_t full_cost(void) {
    int tot, cb;
    bfs_from(0, &tot, &cb);
    int64_t c = (int64_t)(2 * G - tot);
    bfs_from(G, &tot, &cb);
    c += (int64_t)(G - cb);
    return c;
}

static int anneal(int iters) {
    timed_out = 0;
    int64_t cost = full_cost();
    double T0 = 2.0, T1 = 0.2;
    for (int t = 0; t < iters && cost > 0; t++) {
        if ((t & 63) == 0 && elapsed() > TL) {
            timed_out = 1;
            break;
        }
        double T = T0 * pow(T1 / T0, (double)t / iters);
        int i = rndint(DEG);
        int nw = rndint(G);
        int dup = 0;
        for (int j = 0; j < DEG; j++)
            if (S[j] == nw) {
                dup = 1;
                break;
            }
        if (dup) continue;
        int old = S[i];
        S[i] = nw;
        setcol(i);
        int64_t c2 = full_cost();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
        } else {
            S[i] = old;
            setcol(i);
        }
    }
    return cost == 0;
}

int main(int argc, char **argv) {
    if (argc < 7) {
        fprintf(stderr, "usage: d D cap seed TL startG\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    int cap = atoi(argv[3]);
    unsigned long long seed = strtoull(argv[4], NULL, 10);
    TL = atof(argv[5]);
    int startG = atoi(argv[6]);
    tstart = now_s();

    rs = (seed + 1) * 0x9E3779B97F4A7C15ULL ^ 0xD1B54A32D192ED03ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();

    GMAXN = cap / 2;
    if (GMAXN > MAXG) GMAXN = MAXG;
    if (DEG < 3 || DEG > MAXD || DIAM < 3 || GMAXN < DEG) {
        printf("0 0\n");
        return 0;
    }

    int lo = startG;
    if (lo < DEG - 1) lo = DEG - 1;
    int bestG = 0;
    int bestM = 0, bestK = 0;
    int64_t bestR = 1;
    int bestS[MAXD];
    int hi = lo + (lo / 20 > 2 ? lo / 20 : 2);
    int streak = 0;

    while (elapsed() < TL && lo < GMAXN) {
        int span = hi - lo;
        if (span < 1) span = 1;
        int Gt = lo + 1 + rndint(span);
        if (Gt > GMAXN) Gt = GMAXN;
        if (!sample_group(Gt)) continue;
        if (G > GMAXN || G < DEG) continue;

        for (int i = 0; i < DEG; i++) {
            int nw;
            int ok2;
            do {
                nw = rndint(G);
                ok2 = 1;
                for (int j = 0; j < i; j++)
                    if (S[j] == nw) ok2 = 0;
            } while (!ok2);
            S[i] = nw;
        }
        for (int i = 0; i < DEG; i++) setcol(i);

        int iters = 800 + G;
        int ok = anneal(iters);
        if (timed_out && !ok) break;

        if (ok) {
            if (G > bestG) {
                bestG = G;
                bestM = GM;
                bestK = GK;
                bestR = RR;
                memcpy(bestS, S, sizeof(int) * (size_t)DEG);
            }
            if (G > lo) lo = G;
            hi = lo + (lo / 20 > 2 ? lo / 20 : 2);
            streak = 0;
        } else {
            streak++;
            if (streak > 40 && hi - lo > 1) {
                hi = lo + (hi - lo) / 2;
                streak = 0;
            }
        }
    }

    if (bestG == 0) {
        printf("0 0\n");
        return 0;
    }
    setup_group(bestM, bestK, bestR);
    printf("%d %lld\n", 2 * bestG, (long long)bestG * DEG);
    for (int g = 0; g < bestG; g++)
        for (int i = 0; i < DEG; i++)
            printf("%d %d\n", g, bestG + gmul(g, bestS[i]));
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact construction used as a fallback start.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


_MAX_N = 8000  # keeps the C allocations and the bitset check bounded


# ----------------------------------------------------------------------------
# Main build. Safe fallback first (K_{d,d}, or PG(2,q) when it applies), then
# the C Cayley-type search gets most of the time, and only valid, larger
# graphs replace the fallback.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()

    def left():
        return time_limit - (time.monotonic() - start)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2
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

    if D >= 3 and d >= 3 and left() > 12.0:
        cap = min(lib.moore_bound(d, D), _MAX_N)
        budget = left() - 7.0
        if cap > best_n and budget > 2.0:
            try:
                text = lib.run_c(
                    C_SOURCE,
                    [d, D, cap, int(seed) & 0x7FFFFFFF, round(budget, 2), best_n // 2],
                    timeout=budget + 4.0,
                )
                consider(*lib.parse_graph_text(text))
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
