import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact baselines (unchanged from the parent): PG(2, q) and W(q).
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
# C engine: exhaustive-group bi-Cayley search with hill climbing.
#
# Graph model: group G = Z_M x|_R Z_K (order ORD), connection set S of d
# distinct elements. Vertices A_g = g and B_h = ORD + h; A_g ~ B_{g*s} for s in S.
# Left multiplication is an automorphism that is transitive on each side, so
# the diameter is the max eccentricity of A_0 and B_0. The cost is the number
# of vertices unreached from A_0 and from B_0 within DD steps; cost 0 means a
# valid graph. Each candidate costs only two BFS passes.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXD 12
#define MAXORD 16384
#define STEPS 6000

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int d, DD, M, K, R, ORD;
static int gp[MAXORD];
static int S[MAXD];
static int rt[MAXD][MAXORD];
static int lt[MAXD][MAXORD];
static int stampv[2 * MAXORD];
static int qv[2 * MAXORD];
static int stamp = 0;
static int rbuf[MAXORD];

static void set_group(int m, int k, int r) {
    M = m;
    K = k;
    R = r;
    long long p = 1 % M;
    for (int b = 0; b < K; b++) {
        gp[b] = (int)p;
        p = (p * R) % M;
    }
}

static int gmul(int x, int y) {
    int a = x / K, b = x % K, c = y / K, e = y % K;
    long long t = ((long long)a + (long long)gp[b] * (long long)c) % M;
    return (int)(t * K + (b + e) % K);
}

static int ginv(int x) {
    int a = x / K, b = x % K;
    int nb = (K - b) % K;
    long long t = (-((long long)gp[nb] * (long long)a)) % M;
    if (t < 0) t += M;
    return (int)(t * K + nb);
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

/* Choose a random semidirect group of order ord. Returns 1 on success. */
static int pick_group(int ord) {
    int divs[512];
    int nd = 0;
    for (int k = 1; k <= ord && nd < 512; k++)
        if (ord % k == 0) divs[nd++] = k;
    for (int t = 0; t < 20; t++) {
        int k = divs[rint_(nd)];
        int m = ord / k;
        if (k == 1) {
            set_group(ord, 1, 1);
            return 1;
        }
        if (m < 3) continue;
        int cnt = 0;
        for (int r = 1; r < m; r++) {
            if (gcdll(r, m) == 1 && powmod(r, k, m) == 1 % m) rbuf[cnt++] = r;
        }
        if (cnt == 0) continue;
        set_group(m, k, rbuf[rint_(cnt)]);
        return 1;
    }
    return 0;
}

static void update_tables(int j) {
    for (int g = 0; g < ORD; g++) {
        rt[j][g] = gmul(g, S[j]);
        lt[j][g] = gmul(g, ginv(S[j]));
    }
}

/* True if x equals S[k] for some k < n with k != skip. */
static int inset(int x, int n, int skip) {
    for (int k = 0; k < n; k++)
        if (k != skip && S[k] == x) return 1;
    return 0;
}

static int bfs_reach(int src) {
    stamp++;
    int head = 0, tail = 0;
    stampv[src] = stamp;
    qv[tail++] = src;
    for (int lvl = 0; lvl < DD; lvl++) {
        int end = tail;
        while (head < end) {
            int u = qv[head++];
            if (u < ORD) {
                for (int j = 0; j < d; j++) {
                    int v = ORD + rt[j][u];
                    if (stampv[v] != stamp) {
                        stampv[v] = stamp;
                        qv[tail++] = v;
                    }
                }
            } else {
                int h = u - ORD;
                for (int j = 0; j < d; j++) {
                    int v = lt[j][h];
                    if (stampv[v] != stamp) {
                        stampv[v] = stamp;
                        qv[tail++] = v;
                    }
                }
            }
        }
    }
    return tail;
}

static int cost_now(void) {
    return (2 * ORD - bfs_reach(0)) + (2 * ORD - bfs_reach(ORD));
}

static void random_S(void) {
    for (int j = 0; j < d; j++) {
        int x;
        do {
            x = rint_(ORD);
        } while (inset(x, j, -1));
        S[j] = x;
        update_tables(j);
    }
}

/* Hill climbing on the cost with plateau moves. Returns the final cost. */
static int climb(int steps, double dl) {
    random_S();
    int c = cost_now();
    for (int t = 0; t < steps && c > 0; t++) {
        if ((t & 63) == 0 && now_s() > dl) break;
        int j = rint_(d);
        int old = S[j];
        int x;
        do {
            x = rint_(ORD);
        } while (inset(x, d, j));
        S[j] = x;
        update_tables(j);
        int c2 = cost_now();
        if (c2 <= c) {
            c = c2;
        } else {
            S[j] = old;
            update_tables(j);
        }
    }
    return c;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    DD = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int best_n = argc > 5 ? atoi(argv[5]) : 0;
    if (d < 3 || d > MAXD || DD < 3) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 8; w++) rnd();

    double dl = now_s() + tl;
    int lo = best_n / 2 + 1;
    if (lo < d + 1) lo = d + 1;
    int bestOrd = 0, bM = 1, bK = 1, bR = 1;
    int bS[MAXD];
    int fails = 0;

    while (now_s() < dl) {
        if (lo > MAXORD) break;
        int W = 4 + fails / 40;
        if (W > 300) W = 300;
        int ord = lo + rint_(W);
        if (ord > MAXORD) ord = MAXORD;
        if (!pick_group(ord)) {
            fails++;
            continue;
        }
        ORD = ord;
        int c = climb(STEPS, dl);
        if (c == 0) {
            bestOrd = ord;
            bM = M;
            bK = K;
            bR = R;
            memcpy(bS, S, sizeof(int) * (size_t)d);
            lo = ord + 1;
            fails = 0;
        } else {
            fails++;
        }
    }

    if (bestOrd == 0) {
        printf("0 0\n");
        return 0;
    }
    ORD = bestOrd;
    set_group(bM, bK, bR);
    memcpy(S, bS, sizeof(int) * (size_t)d);
    for (int j = 0; j < d; j++) update_tables(j);
    printf("%d %ld\n", 2 * ORD, (long)d * (long)ORD);
    for (int j = 0; j < d; j++)
        for (int g = 0; g < ORD; g++)
            printf("%d %d\n", g, ORD + rt[j][g]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions first, then the C group-lift search.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(3.0, min(0.85 * time_limit, time_limit - 6.0))

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
                return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Group-lift hill climbing in C, seeded with the best known order.
    if 3 <= d <= 12 and D >= 3:
        budget = deadline - time.monotonic() - 1.0
        if budget >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", best_n],
                                timeout=budget + 6.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
