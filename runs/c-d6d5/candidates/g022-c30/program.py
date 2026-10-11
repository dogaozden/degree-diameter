import time

import lib


# ----------------------------------------------------------------------------
# C engine: tabu search over connection sets of Haar-type lifts.
#
# Group G = Z_m x|_R Z_K2 (element (a,b) coded as a*K2+b), with 2G vertices:
# A_g = g and B_h = G+h. A connection set S of DEG distinct group elements
# gives edges A_g -- B_{g*s} for all g and all s in S. Each vertex has
# degree DEG, the graph is bipartite, and left multiplication is an
# automorphism that preserves the sides. So diameter <= DIAM iff a BFS of
# depth DIAM from A_0 and from B_0 reaches all 2G vertices.
#
# Search: tabu search over S with single-element swaps. Each step samples
# NSAMP random swaps, takes the best non-tabu one (aspiration if it beats the
# run's best), and forbids re-inserting the removed element for a short
# tenure. The cost is the number of unreached vertices from the two
# representatives. Groups are drawn with 2G just above the current best, so
# every zero-cost hit is an improvement and is kept.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define NSAMP 80
#define NSTALL 500
#define TT_MIN 5
#define TT_RAND 10
#define MAXDEG 16
#define MAXG 4096
#define BIGCOST 1000000000

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

static int DEG, DIAM, M, K2, G, R;
static int Rpow[MAXG];
static int S[MAXDEG], bestS[MAXDEG];
static int inS[MAXG];
static long long tabu[MAXG];
static int adjv[2 * MAXG * MAXDEG];
static int cnt[2 * MAXG];
static int stampv[2 * MAXG];
static int cstamp = 0;
static int fq[2 * MAXG], nq[2 * MAXG];

static int found = 0, fM = 0, fK2 = 1, fR = 1;
static int fS[MAXDEG];
static int best_n = 0;

/* (a,b)*(c,e) = (a + R^b c, b + e), element index a*K2 + b. */
static inline int gmul(int x, int y) {
    int a = x / K2, b = x % K2;
    int c = y / K2, e = y % K2;
    long long ra = ((long long)a + (long long)Rpow[b] * c) % M;
    int rb = (b + e) % K2;
    return (int)ra * K2 + rb;
}

static void setup_group(int m, int c2, int r) {
    M = m; K2 = c2; R = r; G = m * c2;
    Rpow[0] = 1 % M;
    for (int b = 1; b < K2; b++) Rpow[b] = (int)((long long)Rpow[b - 1] * R % M);
    memset(stampv, 0, sizeof(int) * (size_t)(2 * G));
    cstamp = 0;
}

/* Cost = unreached vertices from A_0 plus from B_0 within DIAM steps. */
static int eval_cost(void) {
    int N = 2 * G;
    for (int i = 0; i < N; i++) cnt[i] = 0;
    for (int j = 0; j < DEG; j++) {
        int s = S[j];
        for (int g = 0; g < G; g++) {
            int a = g, b = G + gmul(g, s);
            adjv[a * DEG + cnt[a]++] = b;
            adjv[b * DEG + cnt[b]++] = a;
        }
    }
    int total = 0;
    for (int rep = 0; rep < 2; rep++) {
        int src = (rep == 0) ? 0 : G;
        if (cstamp >= 2000000000) {
            memset(stampv, 0, sizeof(int) * (size_t)N);
            cstamp = 0;
        }
        cstamp++;
        int fsz = 1, count = 1;
        fq[0] = src;
        stampv[src] = cstamp;
        for (int lvl = 0; lvl < DIAM && fsz > 0; lvl++) {
            int nsz = 0;
            for (int q = 0; q < fsz; q++) {
                int u = fq[q];
                const int *au = adjv + u * DEG;
                for (int e = 0; e < DEG; e++) {
                    int v = au[e];
                    if (stampv[v] != cstamp) {
                        stampv[v] = cstamp;
                        nq[nsz++] = v;
                    }
                }
            }
            count += nsz;
            memcpy(fq, nq, sizeof(int) * (size_t)nsz);
            fsz = nsz;
        }
        total += N - count;
    }
    return total;
}

/* Tabu search for a zero-cost connection set in the current group.
   Returns 1 and leaves S valid if found. */
static int tabu_group(void) {
    for (int i = 0; i < G; i++) { inS[i] = 0; tabu[i] = 0; }
    for (int j = 0; j < DEG; j++) {
        int t;
        do { t = rnd_int(G); } while (inS[t]);
        S[j] = t;
        inS[t] = 1;
    }
    int cur = eval_cost();
    int runbest = cur;
    memcpy(bestS, S, sizeof(int) * (size_t)DEG);
    int stall = 0;
    for (long long step = 1; cur > 0; step++) {
        if ((step & 15) == 0 && elapsed() > DEADLINE) break;
        int bc = BIGCOST, bj = -1, bt = -1;
        for (int s = 0; s < NSAMP; s++) {
            int j = rnd_int(DEG), t = rnd_int(G);
            if (inS[t]) continue;
            int old = S[j];
            S[j] = t; inS[old] = 0; inS[t] = 1;
            int c = eval_cost();
            S[j] = old; inS[t] = 0; inS[old] = 1;
            if (tabu[t] > step && c >= runbest) continue;
            if (c < bc) { bc = c; bj = j; bt = t; }
        }
        if (bj < 0) continue;
        int old = S[bj];
        S[bj] = bt; inS[old] = 0; inS[bt] = 1;
        tabu[old] = step + TT_MIN + rnd_int(TT_RAND);
        cur = bc;
        if (cur < runbest) {
            runbest = cur;
            memcpy(bestS, S, sizeof(int) * (size_t)DEG);
            stall = 0;
        } else if (++stall > NSTALL) {
            break;
        }
    }
    if (runbest == 0) {
        memcpy(S, bestS, sizeof(int) * (size_t)DEG);
        return 1;
    }
    return 0;
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
    if (DEG < 1 || DIAM < 1 || DEG > MAXDEG) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    best_n = start_n;
    static const int CC[13] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16};

    while (elapsed() < DEADLINE) {
        int gmin = best_n / 2 + 1;
        if (gmin < DEG) gmin = DEG;
        if (gmin < 2) gmin = 2;
        if (gmin + 2 > MAXG) break;
        int sp = gmin / 30 + 3;
        int g = gmin + rnd_int(sp);
        if (g > MAXG) g = MAXG;

        int cands[13], nc = 0;
        for (int i = 0; i < 13; i++)
            if (g % CC[i] == 0 && g / CC[i] >= 2) cands[nc++] = CC[i];
        int c2 = cands[rnd_int(nc)];
        int m = g / c2, r = 1;
        if (c2 > 1) {
            int ok = 0;
            for (int tr = 0; tr < 300 && !ok; tr++) {
                int cand = 1 + rnd_int(m - 1);
                if (gcd_i(cand, m) == 1 && powmod(cand, c2, m) == 1 % m) {
                    r = cand;
                    ok = 1;
                }
            }
            if (!ok) { c2 = 1; m = g; r = 1; }
        }
        if (G_check_dummy_unused_guard(0)) break;
        setup_group(m, c2, r);
        if (G < DEG) continue;
        if (tabu_group()) {
            if (2 * G > best_n) {
                best_n = 2 * G;
                found = 1;
                fM = M; fK2 = K2; fR = R;
                memcpy(fS, S, sizeof(int) * (size_t)DEG);
            }
        }
    }

    if (found) {
        setup_group(fM, fK2, fR);
        memcpy(S, fS, sizeof(int) * (size_t)DEG);
        int n = 2 * G;
        printf("%d %d\n", n, G * DEG);
        for (int j = 0; j < DEG; j++) {
            for (int g = 0; g < G; g++) {
                printf("%d %d\n", g, G + gmul(g, S[j]));
            }
        }
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Safe baseline: incidence graph of PG(2, q), diameter 3.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Driver: baselines in Python, then the C tabu search over Haar-type lifts.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        best = (2, [(0, 1)]) if d >= 1 and D >= 1 else (1, [])
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

    # Already at the Moore bound: nothing larger is possible.
    if best_n >= lib.moore_bound(d, D):
        return best

    # Give the C search nearly all of the budget; margins cover parsing and validation.
    remaining = 0.9 * time_limit - (time.monotonic() - start) - 2.0
    if remaining >= 2.0:
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
