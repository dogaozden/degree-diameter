"""Orbit-reduced group voltage lifts, then growth by vertex-pair insertion.

Phase 1 (C): simulated annealing over Z_m x| Z_k semidirect-product lifts, as in the parent.
Phase 2 (C, new): take the best lift (or K_{d,d} if none), then repeatedly insert one
A-vertex and one B-vertex. The new pair takes d-1 edges (a_i, b_i) from a matching and
rewires them to x-b_i and a_i-y, so every degree stays d and the graph stays bipartite.
Bad pairs are then reduced by degree-preserving 2-switches, using a bitset ball computation.
A stage that fails is rolled back to the last valid graph.
"""
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXG 1024
#define MAXN 2048
#define MAXD 32
#define MAXK 4
#define MAXT (MAXD * MAXK)
#define MAXE (MAXG * MAXD)
#define WMAX (MAXN / 64)
#define BIGC 1000000000L
#define LIFT_FRAC 0.55

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int n) { return n <= 0 ? 0 : (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd_i(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

static int powmod_i(int b, int e, int m) {
    long long r = 1 % m, x = b % m;
    while (e > 0) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

/* ---------------- lift stage ---------------- */

static int GM[MAXG * MAXG];
static int GO = 0;
static int DI[MAXT], DJ[MAXT], DS[MAXT];
static int ADJ[MAXN * MAXD];
static int CNT[MAXN];
static int VIS[MAXN];
static int QU[MAXN];
static int STAMP = 0;
static int BE[2 * MAXE + 16];
static int BEcount = 0;
static int best_n = 0;
static int best_half = 0;
static double DEADLINE = 0.0;
static const int KCH[6] = {1, 1, 2, 2, 3, 4};

static void build_group(int m, int k2, int r) {
    int G = m * k2;
    int pw[16];
    pw[0] = 1 % m;
    for (int b = 1; b < k2; b++) pw[b] = (int)((long long)pw[b - 1] * r % m);
    for (int x = 0; x < G; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < G; y++) {
            int c = y / k2, e2 = y % k2;
            int aa = (int)(((long long)a + (long long)pw[b] * c) % m);
            GM[x * G + y] = aa * k2 + (b + e2) % k2;
        }
    }
    GO = G;
}

static int choose_group(int G) {
    int cand[12], nc = 0;
    for (int k2 = 1; k2 <= 12; k2++)
        if (G % k2 == 0 && G / k2 >= 2) cand[nc++] = k2;
    if (nc == 0) return 0;
    int k2 = cand[rndint(nc)];
    int m = G / k2;
    int r = 1;
    if (k2 > 1) {
        for (int t = 0; t < 200; t++) {
            int c = 1 + rndint(m - 1);
            if (gcd_i(c, m) == 1 && powmod_i(c, k2, m) == 1 % m) { r = c; break; }
        }
    }
    build_group(m, k2, r);
    return 1;
}

static void random_darts(int k, int d) {
    int perm[MAXK];
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = perm[i]; perm[i] = perm[j]; perm[j] = tmp;
        }
        for (int i = 0; i < k; i++) {
            int t = l * k + i;
            DI[t] = i;
            DJ[t] = perm[i];
            DS[t] = rndint(GO);
        }
    }
}

static long eval_cost(int k, int d, int D) {
    int G = GO, N = 2 * k * G, T = k * d;
    if (N > MAXN) return BIGC;
    for (int a = 0; a < T; a++)
        for (int b = a + 1; b < T; b++)
            if (DI[a] == DI[b] && DJ[a] == DJ[b] && DS[a] == DS[b]) return BIGC;
    for (int v = 0; v < N; v++) CNT[v] = 0;
    for (int t = 0; t < T; t++) {
        int i = DI[t], j = DJ[t], s = DS[t];
        for (int g = 0; g < G; g++) {
            int a = i * G + g;
            int b = (k + j) * G + GM[g * G + s];
            if (CNT[a] >= d || CNT[b] >= d) return BIGC;
            ADJ[a * MAXD + CNT[a]++] = b;
            ADJ[b * MAXD + CNT[b]++] = a;
        }
    }
    for (int v = 0; v < N; v++) if (CNT[v] != d) return BIGC;

    long total = 0;
    for (int rep = 0; rep < 2 * k; rep++) {
        int src = rep * G;
        STAMP++;
        if (STAMP == 0x7fffffff) { memset(VIS, 0, sizeof(VIS)); STAMP = 1; }
        int head = 0, tail = 0;
        QU[tail++] = src;
        VIS[src] = STAMP;
        for (int lev = 0; lev < D && head < tail; lev++) {
            int end = tail;
            for (; head < end; head++) {
                int u = QU[head];
                for (int c = 0; c < d; c++) {
                    int v = ADJ[u * MAXD + c];
                    if (VIS[v] != STAMP) { VIS[v] = STAMP; QU[tail++] = v; }
                }
            }
        }
        total += N - tail;
    }
    return total;
}

static long anneal(int k, int d, int D, long iters) {
    int G = GO, T = k * d;
    long cur = eval_cost(k, d, D);
    double temp0 = 0.5 * G + 1.0;
    for (long it = 0; it < iters && cur > 0; it++) {
        if ((it & 1023) == 0 && now_s() > DEADLINE) break;
        double frac = (double)it / (double)iters;
        double temp = temp0 * (1.0 - frac) + 0.3;
        if (rndint(2) == 0) {
            int t = rndint(T);
            int old = DS[t];
            int ns = rndint(G);
            if (ns == old) continue;
            DS[t] = ns;
            long c2 = eval_cost(k, d, D);
            if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / temp)) cur = c2;
            else DS[t] = old;
        } else {
            int l = rndint(d);
            int i1 = rndint(k), i2 = rndint(k);
            if (i1 == i2) continue;
            int t1 = l * k + i1, t2 = l * k + i2;
            int tmp = DJ[t1]; DJ[t1] = DJ[t2]; DJ[t2] = tmp;
            long c2 = eval_cost(k, d, D);
            if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / temp)) cur = c2;
            else { tmp = DJ[t1]; DJ[t1] = DJ[t2]; DJ[t2] = tmp; }
        }
    }
    return cur;
}

static void store_best(int k, int d) {
    int G = GO, T = k * d;
    BEcount = 0;
    for (int t = 0; t < T; t++)
        for (int g = 0; g < G; g++) {
            BE[2 * BEcount] = DI[t] * G + g;
            BE[2 * BEcount + 1] = (k + DJ[t]) * G + GM[g * G + DS[t]];
            BEcount++;
        }
    best_n = 2 * k * G;
    best_half = k * G;
}

static void lift_phase(int d, int D) {
    int step = 16, fails = 0;
    while (now_s() < DEADLINE) {
        int k = KCH[rndint(6)];
        int nmin = best_n + step;
        int gmin = (nmin + 2 * k - 1) / (2 * k);
        if (gmin < 2) gmin = 2;
        int G = gmin + rndint(1 + gmin / 12);
        int gcap = MAXN / (2 * k);
        if (gcap > MAXG) gcap = MAXG;
        if (G > gcap) G = gcap;
        if (G < 2) { fails++; continue; }
        if (!choose_group(G)) { fails++; continue; }
        random_darts(k, d);
        long c = anneal(k, d, D, 20000);
        if (c == 0) {
            if (2 * k * GO > best_n) store_best(k, d);
            fails = 0;
            step = step * 2;
            int cap = 16 + best_n / 8;
            if (step > cap) step = cap;
        } else if (++fails >= 4) {
            fails = 0;
            step = step / 2;
            if (step < 2) step = 2;
        }
    }
}

/* ---------------- general d-regular bipartite graph ---------------- */

static int GN = 0, NA = 0, NB = 0;
static int GADJ[MAXN * MAXD];
static int GDEG[MAXN];
static int ALIST[MAXN], BLIST[MAXN];
static int SN_GN = 0, SN_NA = 0, SN_NB = 0;
static int SGADJ[MAXN * MAXD];
static int SALIST[MAXN], SBLIST[MAXN];
static uint64_t RA[MAXN * WMAX], RB[MAXN * WMAX];
static int MARKA[MAXN], MARKB[MAXN];
static int MSTAMP = 0;

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b, int d) {
    for (int c = 0; c < d; c++) if (GADJ[a * MAXD + c] == b) return 1;
    return 0;
}

static void replace_nb(int v, int from, int to, int d) {
    for (int c = 0; c < d; c++)
        if (GADJ[v * MAXD + c] == from) { GADJ[v * MAXD + c] = to; return; }
}

/* Number of unordered pairs at distance > D, via bitset balls. */
static long bad_pairs(int d, int D) {
    int N = GN, W = (N + 63) >> 6;
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N * (size_t)W);
    for (int v = 0; v < N; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            const uint64_t *s = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) o[w] = s[w];
            for (int c = 0; c < d; c++) {
                int u = GADJ[v * MAXD + c];
                const uint64_t *t = cur + (size_t)u * W;
                for (int w = 0; w < W; w++) o[w] |= t[w];
            }
        }
        uint64_t *tmp = cur; cur = nxt; nxt = tmp;
    }
    long tot = 0;
    for (int v = 0; v < N; v++) {
        int cnt = 0;
        for (int w = 0; w < W; w++) cnt += popc64(cur[(size_t)v * W + w]);
        tot += N - cnt;
    }
    return tot / 2;
}

/* Degree-preserving 2-switch annealing on bad pairs. */
static long anneal_general(int d, int D, long iters, double T0, double T1) {
    long cur = bad_pairs(d, D);
    double ratio = T1 / T0;
    for (long it = 0; it < iters && cur > 0; it++) {
        if ((it & 63) == 0 && now_s() > DEADLINE) break;
        double T = T0 * pow(ratio, (double)it / (double)iters);
        int a1 = ALIST[rndint(NA)], a2 = ALIST[rndint(NA)];
        if (a1 == a2) continue;
        int c1 = rndint(d), c2 = rndint(d);
        int b1 = GADJ[a1 * MAXD + c1], b2 = GADJ[a2 * MAXD + c2];
        if (b1 == b2) continue;
        if (has_edge(a1, b2, d) || has_edge(a2, b1, d)) continue;
        GADJ[a1 * MAXD + c1] = b2;
        GADJ[a2 * MAXD + c2] = b1;
        replace_nb(b1, a1, a2, d);
        replace_nb(b2, a2, a1, d);
        long nc = bad_pairs(d, D);
        long delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = nc;
        } else {
            GADJ[a1 * MAXD + c1] = b1;
            GADJ[a2 * MAXD + c2] = b2;
            replace_nb(b1, a2, a1, d);
            replace_nb(b2, a1, a2, d);
        }
    }
    return cur;
}

/* Add one A-vertex x and one B-vertex y joined to each other, with d-1 edges
   a_i-b_i (distinct a's, distinct b's) rewired to x-b_i and a_i-y. Degrees stay d. */
static int insert_pair(int d) {
    if (GN + 2 > MAXN || NA < 2) return 0;
    int x = GN, y = GN + 1;
    ALIST[NA++] = x;
    BLIST[NB++] = y;
    GN += 2;
    GADJ[x * MAXD] = y;
    GADJ[y * MAXD] = x;
    MSTAMP++;
    int cnt = 0;
    long tries = 0;
    while (cnt < d - 1 && tries < 200000) {
        tries++;
        int a = ALIST[rndint(NA - 1)];
        int c = rndint(d);
        int b = GADJ[a * MAXD + c];
        if (MARKA[a] == MSTAMP || MARKB[b] == MSTAMP) continue;
        MARKA[a] = MSTAMP;
        MARKB[b] = MSTAMP;
        GADJ[a * MAXD + c] = y;
        replace_nb(b, a, x, d);
        GADJ[x * MAXD + 1 + cnt] = b;
        GADJ[y * MAXD + 1 + cnt] = a;
        cnt++;
    }
    return cnt == d - 1;
}

static void save_state(void) {
    SN_GN = GN; SN_NA = NA; SN_NB = NB;
    memcpy(SGADJ, GADJ, sizeof(int) * (size_t)GN * MAXD);
    memcpy(SALIST, ALIST, sizeof(int) * (size_t)NA);
    memcpy(SBLIST, BLIST, sizeof(int) * (size_t)NB);
}

static void restore_state(void) {
    GN = SN_GN; NA = SN_NA; NB = SN_NB;
    memcpy(GADJ, SGADJ, sizeof(int) * (size_t)GN * MAXD);
    memcpy(ALIST, SALIST, sizeof(int) * (size_t)NA);
    memcpy(BLIST, SBLIST, sizeof(int) * (size_t)NB);
}

static void init_complete(int d) {
    GN = 2 * d; NA = d; NB = d;
    for (int i = 0; i < d; i++) { ALIST[i] = i; BLIST[i] = d + i; }
    for (int a = 0; a < d; a++)
        for (int j = 0; j < d; j++) {
            GADJ[a * MAXD + j] = d + j;
            GADJ[(d + j) * MAXD + a] = a;
        }
}

static int load_lift(int d) {
    int N = best_n;
    if (N < 2 || N > MAXN) return 0;
    for (int v = 0; v < N; v++) GDEG[v] = 0;
    GN = N;
    for (int e = 0; e < BEcount; e++) {
        int a = BE[2 * e], b = BE[2 * e + 1];
        if (a < 0 || a >= N || b < 0 || b >= N) return 0;
        if (GDEG[a] >= d || GDEG[b] >= d) return 0;
        GADJ[a * MAXD + GDEG[a]++] = b;
        GADJ[b * MAXD + GDEG[b]++] = a;
    }
    NA = NB = 0;
    for (int v = 0; v < N; v++) {
        if (GDEG[v] != d) return 0;
        if (v < best_half) ALIST[NA++] = v;
        else BLIST[NB++] = v;
    }
    return 1;
}

static void grow_phase(int d, int D) {
    long iters = 4000;
    int fails = 0;
    while (now_s() < DEADLINE) {
        save_state();
        if (!insert_pair(d)) { restore_state(); fails++; continue; }
        long c = anneal_general(d, D, iters, 2.0, 0.05);
        if (c == 0) {
            fails = 0;
        } else {
            restore_state();
            if (++fails % 10 == 0 && iters < 200000) iters += iters / 2;
        }
    }
}

static void print_state(int d) {
    long m = (long)NA * d;
    printf("%d %ld\n", GN, m);
    for (int i = 0; i < NA; i++) {
        int a = ALIST[i];
        for (int c = 0; c < d; c++) printf("%d %d\n", a, GADJ[a * MAXD + c]);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 20; w++) rnd64();
    double t_start = now_s();
    double t_end = t_start + tl;
    if (d < 3 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }

    DEADLINE = t_start + LIFT_FRAC * tl;
    lift_phase(d, D);
    if (!(best_n > 0 && load_lift(d) && bad_pairs(d, D) == 0)) init_complete(d);

    DEADLINE = t_end;
    grow_phase(d, D);
    if (bad_pairs(d, D) != 0) init_complete(d);
    print_state(d);
    return 0;
}
"""


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = (2, [(0, 1)])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d == 2:
        n = 2 * D
        consider(n, [(i, (i + 1) % n) for i in range(n)])
        return best

    # Complete bipartite K_{d,d} has diameter 2, so it is valid for D >= 2.
    consider(*lib.haar_graph(d, range(d)))

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(*pg)
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass
        if lib.is_prime_power(d - 1):
            # Moore-optimal for D = 3; nothing larger exists.
            return best

    remaining = time_limit - (time.monotonic() - t0)
    tl_c = remaining - 9.0
    if tl_c >= 2.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(tl_c, 2)],
                            stdin_graph=None, timeout=tl_c + 8.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
