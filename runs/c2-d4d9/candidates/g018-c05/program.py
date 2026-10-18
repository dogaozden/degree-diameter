"""Program: multi-base voltage lifts over metacyclic groups (bold change), with the
bi-Cayley family (one base vertex per side) kept as a second pass.

Construction:
  * Base: A "base" bipartite multigraph with A vertices on each side (A = 1 or 2).
    For A = 2 it is [[x, d-x], [d-x, x]] with 1 <= x <= d/2. Every base vertex has degree d.
  * Group G = Z_m x|_r Z_k (metacyclic). Every base dart (i, j, g) joins (A_i, x) to (B_j, x*g).
    Left multiplication by h in G is an automorphism, so diameter <= D holds iff BFS from
    the identity copy of every base vertex reaches all 2*A*|G| vertices within D steps.
  * Total order 2*A*|G|. A = 2 targets orders above the record with |G| just above ref/4.
  * C engine: random voltages, hill-climbing on the number of unreached (root, vertex)
    pairs, with restarts. Iterative deepening over shuffled candidates.

Safety: Python validates every engine output with lib.is_valid and keeps the best valid
graph, falling back to the known start or K_{d,d}.
"""
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 3300
#define MAXV 13400
#define MAXDEG 8
#define MAXD 16
#define MAXCAND 6000
#define STALL 4000

static int d, DD, A, REFV;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static long gcd_l(long a, long b) {
    while (b) { long t = a % b; a = b; b = t; }
    return a;
}

static long powmod_l(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static long moore_bound(void) {
    if (DD <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * DD;
    long s = 0, p = 1;
    for (int i = 0; i < DD; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

/* ---------------------------------------------------------------- group */

static int GM = 1, GK = 1, GN = 1;
static int N, V, AN;
static int PWR[MAXN];

/* Z_m x|_r Z_k, element (a,b) coded as a*k+b, (a,b)(c,e) = (a + r^b c, b + e). */
static void setup_group(int m, int k, int r) {
    GM = m;
    GK = k;
    GN = m * k;
    N = GN;
    PWR[0] = 1 % m;
    for (int b = 1; b < k; b++) PWR[b] = (int)((long)PWR[b - 1] * r % m);
    V = 2 * A * N;
    AN = A * N;
}

static int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    int aa = (int)(((long)a + (long)PWR[b] * c) % GM);
    return aa * GK + (b + e) % GK;
}

static int ginv(int x) {
    int a = x / GK, b = x % GK;
    int nb = (GK - b) % GK;
    int t = (int)((long)PWR[nb] * a % GM);
    int ca = (GM - t) % GM;
    return ca * GK + nb;
}

/* ---------------------------------------------------------------- base lift */

static int MAT[2][2];
static int NDART;
static int IK[MAXD], JK[MAXD], G[MAXD], bestG[MAXD];
static int adjA[2][MAXDEG], adjB[2][MAXDEG];
static int RG[MAXD][MAXN], LG[MAXD][MAXN];

static void setup_base(int x) {
    if (A == 1) {
        MAT[0][0] = d; MAT[0][1] = 0; MAT[1][0] = 0; MAT[1][1] = 0;
    } else {
        MAT[0][0] = x; MAT[0][1] = d - x; MAT[1][0] = d - x; MAT[1][1] = x;
    }
    NDART = 0;
    for (int i = 0; i < A; i++)
        for (int j = 0; j < A; j++)
            for (int c = 0; c < MAT[i][j]; c++) {
                IK[NDART] = i;
                JK[NDART] = j;
                NDART++;
            }
    for (int i = 0; i < A; i++) {
        int c = 0;
        for (int k = 0; k < NDART; k++) if (IK[k] == i) adjA[i][c++] = k;
    }
    for (int j = 0; j < A; j++) {
        int c = 0;
        for (int k = 0; k < NDART; k++) if (JK[k] == j) adjB[j][c++] = k;
    }
}

static void update_dart(int k) {
    int gi = ginv(G[k]);
    for (int x = 0; x < N; x++) {
        RG[k][x] = gmul(x, G[k]);
        LG[k][x] = gmul(x, gi);
    }
}

static int conflict(int k, int g) {
    for (int t = 0; t < NDART; t++)
        if (t != k && IK[t] == IK[k] && JK[t] == JK[k] && G[t] == g) return 1;
    return 0;
}

static void randomize_voltages(void) {
    for (int k = 0; k < NDART; k++) G[k] = -1 - k;
    for (int k = 0; k < NDART; k++) {
        int g;
        do g = rndint(N); while (conflict(k, g));
        G[k] = g;
    }
    for (int k = 0; k < NDART; k++) update_dart(k);
}

/* ---------------------------------------------------------------- cost */

static int stamp[MAXV];
static int tick = 0;
static int qv[MAXV];

/* Number of vertices within distance DD of root. */
static int reach(int root) {
    if (++tick == 0x7fffffff) {
        memset(stamp, 0, sizeof stamp);
        tick = 1;
    }
    int head = 0, tail = 0;
    stamp[root] = tick;
    qv[tail++] = root;
    for (int lvl = 0; lvl < DD && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qv[head], u;
            if (v < AN) {
                int i = v / N, x = v - i * N;
                for (int t = 0; t < d; t++) {
                    int k = adjA[i][t];
                    u = (A + JK[k]) * N + RG[k][x];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            } else {
                int w = v - AN;
                int j = w / N, y = w - j * N;
                for (int t = 0; t < d; t++) {
                    int k = adjB[j][t];
                    u = IK[k] * N + LG[k][y];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Unreached (root, vertex) pairs over one identity root per base vertex. */
static long cost_all(void) {
    long c = 0;
    for (int i = 0; i < A; i++) {
        c += (long)(V - reach(i * N));
        c += (long)(V - reach((A + i) * N));
    }
    return c;
}

/* ---------------------------------------------------------------- search */

static int climb(double until) {
    randomize_voltages();
    long cur = cost_all(), bc = cur, stall = 0, it = 0;
    while (cur > 0) {
        if ((++it & 7) == 0 && now() > until) return 0;
        if (stall > STALL) {
            randomize_voltages();
            cur = cost_all();
            bc = cur;
            stall = 0;
            continue;
        }
        int k = rndint(NDART);
        int old = G[k];
        int ng = rndint(N);
        if (ng == old || conflict(k, ng)) { stall++; continue; }
        G[k] = ng;
        update_dart(k);
        long nc = cost_all();
        if (nc <= cur || rnd01() < 0.01) {
            cur = nc;
        } else {
            G[k] = old;
            update_dart(k);
        }
        if (cur < bc) { bc = cur; stall = 0; }
        else stall++;
    }
    return 1;
}

typedef struct { int m, k, r, x, N; } Cand;
static Cand cands[MAXCAND];
static int ncand = 0;

static void add_cands(int Nlo, int Nhi) {
    ncand = 0;
    int xmax = (A == 1) ? 1 : (d / 2 >= 1 ? d / 2 : 1);
    for (int Nv = Nlo; Nv <= Nhi; Nv++) {
        for (int k = 2; k <= Nv / 3; k++) {
            if (Nv % k) continue;
            int m = Nv / k;
            if (m < 3) continue;
            int got = 0;
            for (int r = 1; r < m && got < 3; r++) {
                if (gcd_l(r, m) != 1) continue;
                if (powmod_l(r, k, m) != 1 % m) continue;
                got++;
                for (int x = 1; x <= xmax; x++) {
                    if (ncand >= MAXCAND) return;
                    Cand c;
                    c.m = m; c.k = k; c.r = r; c.x = x; c.N = Nv;
                    cands[ncand++] = c;
                }
            }
        }
    }
}

/* ---------------------------------------------------------------- main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed budget [A=1|2] [ref_vertices]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    DD = atoi(argv[2]);
    long seed = atol(argv[3]);
    double budget = atof(argv[4]);
    A = argc > 5 ? atoi(argv[5]) : 2;
    REFV = argc > 6 ? atoi(argv[6]) : 4970;
    if (REFV <= 0) REFV = 4970;

    double t0 = now();
    t_end = t0 + budget - 0.4;

    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXDEG || DD < 2 || (A != 1 && A != 2)) {
        printf("0 0\n");
        return 0;
    }

    long moore = moore_bound();
    int Nlo = (REFV + 2 * A - 1) / (2 * A);
    if (Nlo < 3) Nlo = 3;
    int Nhi = Nlo + Nlo / 10 + 2;
    long cap = moore / (2 * A);
    if (Nhi > cap) Nhi = (int)cap;
    if (Nhi > MAXN) Nhi = MAXN;
    if (Nhi < Nlo) {
        printf("0 0\n");
        return 0;
    }

    add_cands(Nlo, Nhi);
    if (ncand == 0) {
        printf("0 0\n");
        return 0;
    }
    for (int i = ncand - 1; i > 0; i--) {
        int j = rndint(i + 1);
        Cand tmp = cands[i];
        cands[i] = cands[j];
        cands[j] = tmp;
    }

    long best_total = 0;
    int have = 0;
    Cand bestc;
    memset(&bestc, 0, sizeof bestc);

    int cnt = ncand < 50 ? ncand : 50;
    double s0 = budget / (3.0 * (double)cnt);
    if (s0 < 0.15) s0 = 0.15;

    int done = 0;
    for (int round = 0; round < 10 && !done; round++) {
        for (int i = 0; i < ncand; i++) {
            if (now() > t_end - 0.05) { done = 1; break; }
            Cand c = cands[i];
            long total = 2L * A * c.N;
            if (total <= best_total) continue;
            setup_group(c.m, c.k, c.r);
            setup_base(c.x);
            double slice = s0 * (double)(1 << round);
            double rem = t_end - now();
            if (slice > rem) slice = rem;
            if (slice <= 0) { done = 1; break; }
            if (climb(now() + slice)) {
                have = 1;
                best_total = total;
                bestc = c;
                memcpy(bestG, G, sizeof(int) * (size_t)NDART);
            }
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }

    setup_group(bestc.m, bestc.k, bestc.r);
    setup_base(bestc.x);
    printf("%d %ld\n", V, (long)A * d * N);
    for (int i = 0; i < A; i++)
        for (int x = 0; x < N; x++)
            for (int t = 0; t < d; t++) {
                int k = adjA[i][t];
                int y = gmul(x, bestG[k]);
                printf("%d %d\n", i * N + x, (A + JK[k]) * N + y);
            }
    return 0;
}
'''

REF_VERTICES = {(4, 9): 4970}


def known_start(d, D):
    """Best graph Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    if start is None or not lib.is_valid(start[0], start[1], d, D):
        start = lib.haar_graph(d, range(d))   # K_{d,d}: always valid for D >= 2
    best = start
    if best[0] >= lib.moore_bound(d, D):
        return best

    ref = REF_VERTICES.get((d, D), best[0])
    deadline = t0 + 0.80 * time_limit - 2.0

    # Pass 1: bold two-vertex-per-side base lifts. Pass 2: bi-Cayley (one base vertex per side).
    plan = [(2, 0.60), (1, 1.00)]
    for mode, frac in plan:
        remaining = deadline - time.monotonic()
        budget = remaining * frac
        if budget < 1.0:
            continue
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), mode, ref],
                             timeout=budget + 8)
            n, edges = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, edges, d, D):
                best = (n, edges)
        except Exception:
            pass   # keep the best valid graph so far
    return best
