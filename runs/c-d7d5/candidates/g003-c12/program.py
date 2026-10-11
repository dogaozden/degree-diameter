import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over the voltages of bi-Cayley lifts.
#
# Group G = Z_M x| Z_K2 (r^K2 = 1 mod M), elements coded as a*K2 + b with
# (a, b)(c, e) = (a + r^b c, b + e), the same convention as lib.semidirect_group.
# Base: KK vertices per side and Dd layers. Each layer is a permutation P[l]
# of range(KK) plus voltages S[l][i], so every vertex has degree exactly Dd.
# Dart (i, j, s) of layer l joins A_{i,g} to B_{j, g*s} for all g in G.
# Left multiplication is an automorphism, so BFS from the 2*KK block
# representatives decides the diameter.
#
# Cost = unreached (representative, vertex) pairs + PEN * duplicate darts.
# Moves: change one voltage, or swap two destinations inside one layer.
# The C program samples groups near (best order / base size) itself, anneals
# each one, keeps the largest valid lift above the Python-provided bound and
# prints it. It uses wall-clock time and runs until its time budget is spent.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 64
#define MAXK 8
#define MAXG 8192
#define PEN 1000

static int Dd = 3, DD = 3;
static int KK = 1, GM = 1, GK2 = 1, GG = 1, NN = 2;
static long long gpow[64];
static int P[MAXD][MAXK], S[MAXD][MAXK];
static int bP[MAXD][MAXK], bS[MAXD][MAXK];
static int bK = 1, bM = 1, bK2 = 1, bR = 1;
static int have_best = 0;
static int best_n = 0;

static int capN = 0;
static int *adj = NULL, *deg = NULL, *vis = NULL, *que = NULL;
static int stamp = 0;
static uint64_t rs = 88172645463325252ULL;
static double deadline = 0.0;
static int timed_out = 0;

static uint64_t nxt(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int n) { return (int)(nxt() % (uint64_t)n); }

static double urand(void) {
    return (double)(nxt() >> 11) * (1.0 / 9007199254740992.0);
}

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static void set_group(int m, int k2, int r) {
    GM = m;
    GK2 = k2;
    GG = m * k2;
    long long p = 1 % m;
    for (int b = 0; b < k2; b++) {
        gpow[b] = p;
        p = (p * r) % m;
    }
}

static int gmul(int x, int y) {
    int a = x / GK2, b = x % GK2, c = y / GK2, e = y % GK2;
    long long na = ((long long)a + gpow[b] * (long long)c) % GM;
    return (int)na * GK2 + (b + e) % GK2;
}

static void ensure_cap(int N) {
    if (N <= capN) return;
    free(adj);
    free(deg);
    free(vis);
    free(que);
    capN = N;
    adj = (int *)malloc(sizeof(int) * (size_t)N * (size_t)Dd);
    deg = (int *)malloc(sizeof(int) * (size_t)N);
    vis = (int *)calloc((size_t)N, sizeof(int));
    que = (int *)malloc(sizeof(int) * (size_t)N);
    if (!adj || !deg || !vis || !que) {
        printf("0 0\n");
        exit(0);
    }
}

static void build_adj(void) {
    memset(deg, 0, sizeof(int) * (size_t)NN);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < KK; i++) {
            int j = P[l][i], s = S[l][i];
            for (int g = 0; g < GG; g++) {
                int a = i * GG + g;
                int b = (KK + j) * GG + gmul(g, s);
                adj[a * Dd + deg[a]++] = b;
                adj[b * Dd + deg[b]++] = a;
            }
        }
    }
}

static long long cost_eval(void) {
    build_adj();

    long long dup = 0;
    for (int l1 = 0; l1 < Dd; l1++)
        for (int l2 = l1 + 1; l2 < Dd; l2++)
            for (int i = 0; i < KK; i++)
                if (P[l1][i] == P[l2][i] && S[l1][i] == S[l2][i]) dup++;

    int reps[2 * MAXK];
    int nr = 0;
    for (int i = 0; i < KK; i++) reps[nr++] = i * GG;
    for (int j = 0; j < KK; j++) reps[nr++] = (KK + j) * GG;

    long long total = 0;
    for (int r = 0; r < nr; r++) {
        int src = reps[r];
        stamp++;
        int head = 0, tail = 0;
        vis[src] = stamp;
        que[tail++] = src;
        for (int lvl = 0; lvl < DD && head < tail; lvl++) {
            int end = tail;
            while (head < end) {
                int u = que[head++];
                for (int k = 0; k < Dd; k++) {
                    int v = adj[u * Dd + k];
                    if (vis[v] != stamp) {
                        vis[v] = stamp;
                        que[tail++] = v;
                    }
                }
            }
        }
        total += NN - tail;
    }
    return total + (long long)PEN * dup;
}

static void random_init(void) {
    for (int l = 0; l < Dd; l++) {
        int perm[MAXK];
        for (int i = 0; i < KK; i++) perm[i] = i;
        for (int i = KK - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i];
            perm[i] = perm[j];
            perm[j] = t;
        }
        for (int i = 0; i < KK; i++) {
            P[l][i] = perm[i];
            S[l][i] = rndint(GG);
        }
    }
}

static long long anneal(long iters, double T0) {
    long long c = cost_eval();
    for (long t = 0; t < iters && c > 0; t++) {
        if ((t & 127) == 0 && now_s() > deadline) {
            timed_out = 1;
            break;
        }
        double temp = T0 * (1.0 - (double)t / (double)iters) + 0.05;
        int l = rndint(Dd);
        int i = rndint(KK);
        int swap_kind = (KK >= 2 && rndint(4) == 0);
        if (swap_kind) {
            int i2 = rndint(KK - 1);
            if (i2 >= i) i2++;
            int tmp = P[l][i];
            P[l][i] = P[l][i2];
            P[l][i2] = tmp;
            long long c2 = cost_eval();
            if (c2 <= c || urand() < exp(-(double)(c2 - c) / temp)) {
                c = c2;
            } else {
                tmp = P[l][i];
                P[l][i] = P[l][i2];
                P[l][i2] = tmp;
            }
        } else {
            int old = S[l][i];
            int nw = rndint(GG);
            if (nw == old) continue;
            S[l][i] = nw;
            long long c2 = cost_eval();
            if (c2 <= c || urand() < exp(-(double)(c2 - c) / temp)) {
                c = c2;
            } else {
                S[l][i] = old;
            }
        }
    }
    return c;
}

static long long gcdll(long long a, long long b) {
    while (b) {
        long long t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static const int K2S[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};

static void sample_group(long long target, int *om, int *ok2, int *orr) {
    int k2 = K2S[rndint(20)];
    long long m = target / k2;
    if (m < 2) m = 2;
    int r = 1;
    if (k2 > 1 && m > 2) {
        for (int t = 0; t < 80; t++) {
            long long c = 2 + rndint((int)(m - 2));
            if (gcdll(c, m) == 1 && powmod(c, k2, m) == 1 % m) {
                r = (int)c;
                break;
            }
        }
    }
    *om = (int)m;
    *ok2 = k2;
    *orr = r;
}

int main(int argc, char **argv) {
    Dd = argc > 1 ? atoi(argv[1]) : 3;
    DD = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double secs = argc > 4 ? atof(argv[4]) : 10.0;
    int min_n = argc > 5 ? atoi(argv[5]) : 0;

    if (Dd < 1 || Dd > MAXD || DD < 1) {
        printf("0 0\n");
        return 0;
    }

    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 8; w++) nxt();

    double t0 = now_s();
    deadline = t0 + secs;
    best_n = min_n;

    static const int Kchoices[9] = {1, 2, 2, 3, 3, 4, 4, 5, 6};
    const long ITERS = 12000;

    while (!timed_out && now_s() < deadline) {
        int Kc = Kchoices[rndint(9)];
        long long base = best_n / (2 * Kc);
        long long span = base / 8 + 1;
        long long target = base + 1 + rndint((int)span);
        if (target < 2) target = 2;

        int m, k2, r;
        sample_group(target, &m, &k2, &r);
        set_group(m, k2, r);
        if (GG > MAXG) continue;

        KK = Kc;
        NN = 2 * KK * GG;
        if (NN <= best_n) continue;

        ensure_cap(NN);
        random_init();
        long long c = anneal(ITERS, 2.0);
        if (c == 0 && NN > best_n) {
            best_n = NN;
            have_best = 1;
            bK = KK;
            bM = m;
            bK2 = k2;
            bR = r;
            memcpy(bP, P, sizeof(P));
            memcpy(bS, S, sizeof(S));
        }
    }

    if (!have_best) {
        printf("0 0\n");
        return 0;
    }

    set_group(bM, bK2, bR);
    KK = bK;
    NN = 2 * KK * GG;
    Dd = Dd;
    memcpy(P, bP, sizeof(P));
    memcpy(S, bS, sizeof(S));

    printf("%d %d\n", NN, Dd * KK * GG);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < KK; i++) {
            int j = P[l][i], s = S[l][i];
            for (int g = 0; g < GG; g++) {
                int a = i * GG + g;
                int b = (KK + j) * GG + gmul(g, s);
                printf("%d %d\n", a, b);
            }
        }
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact and near-exact constructions used as the starting point.
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
# Python glue: exact constructions, then one C anneal run from the best known order.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
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

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best  # exact Moore-type optimum for D = 3

        # Araujo-Pardo & Lopez record family when d - 2 is a prime power (D = 3).
        if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                n, e = lib.araujo_lopez_graph(d - 2)
                consider(n, e)
            except Exception:
                pass

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search in C, seeded with the best known order as a lower bound.
    if d >= 3 and D >= 3:
        c_budget = deadline - time.monotonic() - 1.0
        remaining = time_limit - (time.monotonic() - start) - 2.5
        if c_budget >= 2.0 and remaining >= c_budget:
            try:
                out = lib.run_c(C_SOURCE,
                                [d, D, seed & 0xFFFFFFFF, f"{c_budget:.2f}", best_n],
                                timeout=remaining)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
