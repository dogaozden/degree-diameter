import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: tabu search over voltage lifts of semidirect products
# Z_m x| Z_k2 with a base of K A-vertices and K B-vertices.
#
# Model: A_i,g = i*G + g and B_j,h = (K+j)*G + h. Dart t = (i, j, s) joins
# A_i,g to B_j,g*s for every g. Each layer is a permutation between the
# A-blocks and the B-blocks, so every vertex has degree DEG. Left
# multiplication is an automorphism, so diameter <= D iff every one of the
# 2K block representatives reaches all vertices within D steps.
#
# Coverage is computed with bitmasks: bit r of mask[v] is set when block
# representative r reaches v within the current depth. One round is a pass
# over the darts, so the cost of an evaluation is about D * T * G.
#
# Search: tabu search. Each step samples a set of single-dart moves (change
# a voltage, or swap two targets inside a layer), applies the best allowed
# move even when it is worse, and forbids reversing it for a short tenure.
# An aspiration rule accepts a tabu move if it beats the run's best cost.
# Duplicate darts add a large penalty, so the search can leave them.
# A run restarts from a fresh random lift after a stall.
#
# Timing: the deadline is wall-clock (timespec_get) from program start.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 8192
#define MAXT 512
#define NBMAX 12
#define BIGC 1000000
#define SAMPLE 24
#define TABU_BASE 6
#define TABU_RAND 8
#define STALL 2500

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
static double rnd_unit(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)(ts.tv_sec - T0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - T0.tv_nsec);
}

static int DEG, DIAM;
static int K, K2, M, G, T, R, NB, N;
static int Rpow[64];
static int dI[MAXT], dJ[MAXT], dS[MAXT];
static int bJ[MAXT], bS[MAXT];
static int tabu_until[MAXT];
static unsigned int curm[MAXN], nxtm[MAXN];
static unsigned char pc[1 << NBMAX];
static int best_n = 0, best_m = 0;
static int *best_e = NULL;

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

/* (a,b)*(c,e) = (a + r^b c, b + e), element index a*K2 + b. */
static inline int gmul(int x, int y) {
    int a = x / K2, b = x % K2;
    int c = y / K2, e = y % K2;
    int ra = (int)(((long long)a + (long long)Rpow[b] * c) % M);
    int rb = (b + e) % K2;
    return ra * K2 + rb;
}

static void setup_group(int k, int c2, int m, int r) {
    K = k; K2 = c2; M = m; R = r;
    G = m * c2;
    NB = 2 * K;
    N = NB * G;
    T = DEG * K;
    Rpow[0] = 1 % M;
    for (int b = 1; b < K2; b++) Rpow[b] = (int)((long long)Rpow[b - 1] * R % M);
}

/* Cost = dup * BIGC + number of uncovered (block representative, vertex) pairs. */
static int eval_cost(void) {
    int dup = 0;
    for (int t1 = 0; t1 < T; t1++)
        for (int t2 = t1 + 1; t2 < T; t2++)
            if (dI[t1] == dI[t2] && dJ[t1] == dJ[t2] && dS[t1] == dS[t2]) dup++;
    for (int v = 0; v < N; v++) curm[v] = 0;
    for (int r = 0; r < NB; r++) curm[r * G] |= 1u << r;
    for (int lvl = 0; lvl < DIAM; lvl++) {
        memcpy(nxtm, curm, sizeof(unsigned int) * (size_t)N);
        for (int t = 0; t < T; t++) {
            int ai = dI[t] * G, bj = (K + dJ[t]) * G, s = dS[t];
            for (int g = 0; g < G; g++) {
                int a = ai + g, b = bj + gmul(g, s);
                nxtm[a] |= curm[b];
                nxtm[b] |= curm[a];
            }
        }
        memcpy(curm, nxtm, sizeof(unsigned int) * (size_t)N);
    }
    long long covered = 0;
    for (int v = 0; v < N; v++) covered += pc[curm[v]];
    long long unc = (long long)NB * N - covered;
    return dup * BIGC + (int)unc;
}

static void random_init(void) {
    for (int l = 0; l < DEG; l++) {
        int p[8];
        for (int i = 0; i < K; i++) p[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rnd_int(i + 1);
            int tmp = p[i]; p[i] = p[j]; p[j] = tmp;
        }
        for (int i = 0; i < K; i++) {
            int t = l * K + i;
            dI[t] = i;
            dJ[t] = p[i];
            dS[t] = rnd_int(G);
        }
    }
}

/* Tabu search from the current random lift. Returns the best cost; on return
   dJ/dS hold the best configuration found. */
static int run_tabu(void) {
    int cost = eval_cost();
    int bestc = cost;
    memcpy(bJ, dJ, sizeof(int) * (size_t)T);
    memcpy(bS, dS, sizeof(int) * (size_t)T);
    for (int t = 0; t < T; t++) tabu_until[t] = 0;
    int stall = 0;
    for (long it = 0; bestc > 0 && stall < STALL; it++) {
        if ((it & 15) == 0 && elapsed() > DEADLINE) break;
        int bc = -1, btype = -1, bt1 = -1, bt2 = -1, bv = 0, nt = 0;
        for (int s = 0; s < SAMPLE; s++) {
            int type, t1 = -1, t2 = -1, v = 0, c;
            if (K > 1 && rnd_unit() < 0.25) {
                int l = rnd_int(DEG);
                int i1 = rnd_int(K), i2 = rnd_int(K);
                if (i1 == i2) continue;
                t1 = l * K + i1;
                t2 = l * K + i2;
                type = 1;
                int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
                c = eval_cost();
                tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
            } else {
                t1 = rnd_int(T);
                v = rnd_int(G);
                if (v == dS[t1]) continue;
                type = 0;
                int old = dS[t1];
                dS[t1] = v;
                c = eval_cost();
                dS[t1] = old;
            }
            int tabu = (tabu_until[t1] > it) || (t2 >= 0 && tabu_until[t2] > it);
            if (tabu && c >= bestc) continue;
            if (bc < 0 || c < bc) {
                bc = c; btype = type; bt1 = t1; bt2 = t2; bv = v; nt = 1;
            } else if (c == bc) {
                nt++;
                if (rnd_int(nt) == 0) {
                    btype = type; bt1 = t1; bt2 = t2; bv = v;
                }
            }
        }
        if (btype < 0) { stall++; continue; }
        int ten = (int)it + TABU_BASE + rnd_int(TABU_RAND);
        if (btype == 0) {
            dS[bt1] = bv;
            tabu_until[bt1] = ten;
        } else {
            int tmp = dJ[bt1]; dJ[bt1] = dJ[bt2]; dJ[bt2] = tmp;
            tabu_until[bt1] = ten;
            tabu_until[bt2] = ten;
        }
        if (bc < bestc) {
            bestc = bc;
            memcpy(bJ, dJ, sizeof(int) * (size_t)T);
            memcpy(bS, dS, sizeof(int) * (size_t)T);
            stall = 0;
        } else {
            stall++;
        }
    }
    memcpy(dJ, bJ, sizeof(int) * (size_t)T);
    memcpy(dS, bS, sizeof(int) * (size_t)T);
    return bestc;
}

static void emit(void) {
    int m = T * G;
    free(best_e);
    best_e = malloc(sizeof(int) * 2 * (size_t)m);
    int idx = 0;
    for (int t = 0; t < T; t++) {
        for (int g = 0; g < G; g++) {
            best_e[idx++] = dI[t] * G + g;
            best_e[idx++] = (K + dJ[t]) * G + gmul(g, dS[t]);
        }
    }
    best_m = m;
    best_n = N;
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
    best_n = argc > 5 ? atoi(argv[5]) : 0;
    best_m = 0;
    if (DEG < 1 || DIAM < 1 || DEG * 3 > MAXT) {
        printf("0 0\n");
        return 0;
    }
    for (int x = 0; x < (1 << NBMAX); x++) {
        int c = 0, y = x;
        while (y) { c += y & 1; y >>= 1; }
        pc[x] = (unsigned char)c;
    }
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    static const int kc[5] = {1, 1, 2, 2, 3};
    while (elapsed() < DEADLINE) {
        int k = kc[rnd_int(5)];
        int gmin = best_n / (2 * k) + 1;
        int spread = gmin / 6 + 2;
        int g = gmin + rnd_int(spread);
        if (g < 2) g = 2;
        int opts[32], no = 0;
        for (int c = 1; c <= 12; c++)
            if (g % c == 0 && g / c >= 2) opts[no++] = c;
        int c2 = opts[rnd_int(no)];
        int m = g / c2, r = 1;
        if (c2 > 1) {
            int found = 0;
            for (int tr = 0; tr < 200 && !found; tr++) {
                int cand = 1 + rnd_int(m - 1);
                if (gcd_i(cand, m) == 1 && powmod(cand, c2, m) == 1 % m) {
                    r = cand;
                    found = 1;
                }
            }
            if (!found) {
                c2 = 1;
                m = g;
                r = 1;
            }
        }
        setup_group(k, c2, m, r);
        if (N > MAXN) continue;
        random_init();
        int bc = run_tabu();
        if (bc == 0 && eval_cost() == 0 && N > best_n) emit();
    }

    if (best_m > 0) {
        printf("%d %d\n", best_n, best_m);
        for (int i = 0; i < best_m; i++)
            printf("%d %d\n", best_e[2 * i], best_e[2 * i + 1]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Safe baseline families.
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
# Driver: safe baselines in Python, then the C tabu search with nearly all the budget.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
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

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D >= 4 and time.monotonic() - start < 0.3 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Already at the Moore bound: nothing larger is possible.
    if best_n >= lib.moore_bound(d, D):
        return best

    # Nearly all of the budget goes to the C search. The reserve covers the
    # one-off C compile, parsing and validation.
    remaining = 0.92 * time_limit - (time.monotonic() - start) - 1.5
    if remaining >= 1.0:
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
