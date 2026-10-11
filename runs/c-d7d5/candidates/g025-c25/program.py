import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact baselines (unchanged): PG(2,q) incidence and W(q) quadrangle incidence.
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
# C engine: a DIFFERENT search from the parent. Instead of breakout clause
# weighting, it runs simulated annealing over bi-Cayley voltage assignments
# on semidirect groups Z_m x| Z_k (K base pairs, d dart layers). Group
# multiplication is precomputed once per group as a table, and each cost
# evaluation is a depth-limited BFS from one representative per base class
# (left translations are automorphisms, so these representatives suffice).
# Cost = unreached (representative, vertex) pairs + PEN * duplicate darts.
#
# Vertices: A_{i,g} = i*G+g, B_{j,h} = (K+j)*G+h.
# Layer l joins A_{i,g} to B_{P[l][i], g*S[l][i]}.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define MAXD 64
#define MAXK 3
#define MAXG 2048
#define PEN 4
#define ITERS 400000L
#define T0 2.0

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }

static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int Dd = 3, DD = 3;
static int GM = 1, GK = 1, GG = 1;
static int gpow[64];
static double deadline = 0.0;

static int mt[MAXG * MAXG];
static int inv_el[MAXG];

static int K = 1, G = 1, NN = 2;
static int P[MAXD][MAXK], IP[MAXD][MAXK], S[MAXD][MAXK];

static int vis_arr[2 * MAXK * MAXG];
static int qu_arr[2 * MAXK * MAXG];
static int stamp_ = 0;

static void set_group(int m, int k, int r) {
    GM = m;
    GK = k;
    GG = m * k;
    long long p = 1 % m;
    for (int b = 0; b < k; b++) {
        gpow[b] = (int)p;
        p = (p * r) % m;
    }
}

static int gmul(int x, int y) {
    int a = x / GK, b = x % GK;
    int c = y / GK, d = y % GK;
    long long t = ((long long)a + (long long)gpow[b] * (long long)c) % GM;
    return (int)t * GK + (b + d) % GK;
}

static void build_table(void) {
    int g = GG;
    for (int x = 0; x < g; x++)
        for (int y = 0; y < g; y++)
            mt[x * g + y] = gmul(x, y);
    for (int x = 0; x < g; x++)
        for (int y = 0; y < g; y++)
            if (mt[x * g + y] == 0) {
                inv_el[x] = y;
                break;
            }
}

static long long raw_cost(void) {
    long long raw = 0;
    int KG = K * G;
    for (int r = 0; r < 2 * K; r++) {
        int src = (r < K) ? r * G : KG + (r - K) * G;
        stamp_++;
        int head = 0, tail = 0;
        vis_arr[src] = stamp_;
        qu_arr[tail++] = src;
        for (int lvl = 0; lvl < DD; lvl++) {
            int end = tail;
            if (head == end) break;
            while (head < end) {
                int u = qu_arr[head++];
                if (u < KG) {
                    int i = u / G, g = u - i * G;
                    for (int l = 0; l < Dd; l++) {
                        int j = P[l][i], s = S[l][i];
                        int v = (K + j) * G + mt[g * G + s];
                        if (vis_arr[v] != stamp_) {
                            vis_arr[v] = stamp_;
                            qu_arr[tail++] = v;
                        }
                    }
                } else {
                    int x = u - KG;
                    int j = x / G, h = x - j * G;
                    for (int l = 0; l < Dd; l++) {
                        int i = IP[l][j], s = S[l][i];
                        int g = mt[h * G + inv_el[s]];
                        int v = i * G + g;
                        if (vis_arr[v] != stamp_) {
                            vis_arr[v] = stamp_;
                            qu_arr[tail++] = v;
                        }
                    }
                }
            }
        }
        raw += NN - tail;
    }
    return raw;
}

static int dup_count(void) {
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < Dd; l1++)
            for (int l2 = l1 + 1; l2 < Dd; l2++)
                if (P[l1][i] == P[l2][i] && S[l1][i] == S[l2][i])
                    dup++;
    return dup;
}

static long long cost_now(void) {
    long long raw = raw_cost();
    int dup = dup_count();
    return raw + (long long)PEN * dup;
}

static void random_state(void) {
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) P[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = P[l][i];
            P[l][i] = P[l][j];
            P[l][j] = t;
        }
        for (int i = 0; i < K; i++) {
            IP[l][P[l][i]] = i;
            S[l][i] = rint_(G);
        }
    }
}

static void swap_p(int l, int i1, int i2) {
    int t = P[l][i1];
    P[l][i1] = P[l][i2];
    P[l][i2] = t;
    IP[l][P[l][i1]] = i1;
    IP[l][P[l][i2]] = i2;
}

/* Simulated annealing on the current group. Returns final cost; 0 means valid. */
static long long anneal(long iters) {
    long long cur = cost_now();
    for (long it = 0; it < iters && cur > 0; it++) {
        if ((it & 255) == 0 && now_s() > deadline) break;
        double T = T0 * (1.0 - (double)it / (double)iters) + 0.03;
        if (K >= 2 && rint_(5) == 0) {
            int l = rint_(Dd), i1 = rint_(K), i2 = rint_(K - 1);
            if (i2 >= i1) i2++;
            swap_p(l, i1, i2);
            long long nw = cost_now();
            if (nw <= cur || rnd01() < exp(-(double)(nw - cur) / T)) {
                cur = nw;
            } else {
                swap_p(l, i1, i2);
            }
        } else {
            int l = rint_(Dd), i = rint_(K);
            int old = S[l][i];
            S[l][i] = rint_(G);
            long long nw = cost_now();
            if (nw <= cur || rnd01() < exp(-(double)(nw - cur) / T)) {
                cur = nw;
            } else {
                S[l][i] = old;
            }
        }
    }
    return cur;
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

static const int KF[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16,
                         18, 20, 21, 24, 27, 28, 30, 32, 36, 40};

/* Picks k and m with m*k >= target and a valid semidirect parameter r. */
static void sample_group(long long target, int *oM, int *oK, int *oR) {
    int nk = (int)(sizeof(KF) / sizeof(KF[0]));
    int k = KF[rint_(nk)];
    long long m = (target + k - 1) / k;
    if (m < 2) m = 2;
    int r = 1;
    if (k > 1 && m > 2) {
        for (int t = 0; t < 200; t++) {
            long long c = 2 + (long long)rint_((int)(m - 2));
            if (gcdll(c, m) == 1 && powmod(c, k, m) == 1 % m) {
                r = (int)c;
                break;
            }
        }
    }
    *oM = (int)m;
    *oK = k;
    *oR = r;
}

int main(int argc, char **argv) {
    Dd = argc > 1 ? atoi(argv[1]) : 3;
    DD = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;
    int min_n = argc > 5 ? atoi(argv[5]) : 0;

    if (Dd < 1 || Dd > MAXD || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 4; w++) rnd();

    double t0 = now_s();
    deadline = t0 + tl;

    int best_n = min_n;
    int have = 0;
    int bK = 1, bG = 1, bM = 1, bKk = 1, bR = 1;
    int bP[MAXD][MAXK], bS[MAXD][MAXK];
    memset(bP, 0, sizeof(bP));
    memset(bS, 0, sizeof(bS));
    long long fails = 0;

    while (now_s() < deadline) {
        int k_ = (rint_(100) < 70) ? 1 : ((rint_(100) < 80) ? 2 : 3);
        K = k_;
        long long need = (long long)best_n + 1;
        long long gt = (need + 2LL * K - 1) / (2LL * K);
        if (gt < 2) gt = 2;
        long long span = gt / 30 + 2;
        long long extra = fails / 30;
        if (extra > gt / 8) extra = gt / 8;
        span += extra;
        long long g = gt + (long long)rint_((int)span);

        int M, Kk, R;
        sample_group(g, &M, &Kk, &R);
        set_group(M, Kk, R);
        G = GG;
        if (G > MAXG) continue;
        NN = 2 * K * G;
        if (NN <= best_n) continue;

        build_table();
        random_state();
        long long c = anneal(ITERS);
        if (c == 0) {
            memcpy(bP, P, sizeof(P));
            memcpy(bS, S, sizeof(S));
            bK = K;
            bG = G;
            bM = M;
            bKk = Kk;
            bR = R;
            best_n = NN;
            have = 1;
            fails = 0;
        } else {
            fails++;
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    set_group(bM, bKk, bR);
    int n = 2 * bK * bG;
    long m = (long)Dd * bK * bG;
    printf("%d %ld\n", n, m);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < bK; i++) {
            for (int g = 0; g < bG; g++) {
                int a = i * bG + g;
                int b = (bK + bP[l][i]) * bG + gmul(g, bS[l][i]);
                printf("%d %d\n", a, b);
            }
        }
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions first, then the C annealer, then validation.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(3.0, min(0.90 * time_limit, time_limit - 5.0))

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

    # Exact constructions.
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

    # Simulated annealing over bi-Cayley voltage assignments, seeded with the best order so far.
    if d >= 3 and D >= 3:
        c_budget = deadline - time.monotonic() - 1.5
        if c_budget >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{c_budget:.2f}", best_n],
                                timeout=time_limit - 3.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
