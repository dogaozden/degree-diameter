import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact baselines.
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
# Group tables. A group of order G is passed to C as its multiplication table.
# Families: affine group AGL(1,q) = {x -> a x + b} (non-abelian, order q(q-1)),
# semidirect products Z_m x| Z_k (includes cyclic Z_G with k = 1).
# ----------------------------------------------------------------------------

_KF = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 24, 27, 28, 30, 32, 36, 40]
_GF_CACHE = {}


def _agl_table(q):
    """Multiplication table of AGL(1,q); element (a, b) is coded as (a-1)*q + b, identity 0."""
    if q not in _GF_CACHE:
        _GF_CACHE[q] = lib.GF(q)
    F = _GF_CACHE[q]
    A, B = [], []
    for a in range(1, q):
        for b in range(q):
            A.append(a)
            B.append(b)
    A = np.array(A, dtype=np.int64)
    B = np.array(B, dtype=np.int64)
    # (a,b)(c,d) = (ac, ad + b)
    pa = F.mul_table[A[:, None], A[None, :]]
    pb = F.add_table[F.mul_table[A[:, None], B[None, :]], B[:, None]]
    return ((pa - 1) * q + pb).astype(np.int64)


def _semi_table(m, k, r):
    """Multiplication table of Z_m x| Z_k with (a,b)(c,d) = (a + r^b c, b + d); element coded a*k+b."""
    G = m * k
    X = np.arange(G, dtype=np.int64)
    a = X // k
    b = X % k
    pw = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    return ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k


def _group_table(G, rng):
    """Pick a group of order G: AGL(1,q) when G = q(q-1), else a random semidirect product (or cyclic)."""
    if rng.random() < 0.6:
        for q in range(3, G + 2):
            if q * (q - 1) == G and lib.is_prime_power(q):
                return _agl_table(q)
    ks = [k for k in _KF if G % k == 0 and G // k >= 3]
    rng.shuffle(ks)
    for k in ks:
        m = G // k
        for _ in range(100):
            r = rng.randrange(2, m)
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                return _semi_table(m, k, r)
    return _semi_table(G, 1, 1)


# ----------------------------------------------------------------------------
# C engine: bi-Cayley-type lift search over a given group table.
#
# Vertices: A_{i,g} = i*G+g, B_{j,h} = (K+j)*G+h. Dart (l, i) joins
# A_{i,g} to B_{P[l][i], g*S[l][i]}. Cost = unreached rep-vertex pairs within
# DD steps + PEN * duplicate darts. Cost 0 is a valid graph of order 2*K*G.
# Left multiplication by the group is an automorphism, so BFS from the 2K
# block representatives suffices. The engine stops at the first valid lift.
#
# Input (stdin): "G m" then m = G*G lines "u v" with u = x*G+y, v = x*y.
# Args: d D seed time_limit min_n K.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 64
#define MAXK 3
#define PEN 1000
#define POLISH_T 80
#define ITERS 20000

typedef struct {
    int K;
    int P[MAXD][MAXK];
    int S[MAXD][MAXK];
} Cfg;

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }

static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int Dd = 3, DD = 3, KFIX = 1;
static int GG = 1;
static int *MT = NULL;
static double deadline = 0.0;

static int cap = 0;
static int *g_adj = NULL, *g_cnt = NULL, *g_vis = NULL, *g_q = NULL;
static int g_stamp = 0;

static void ensure_cap(int N) {
    if (N <= cap) return;
    free(g_adj);
    free(g_cnt);
    free(g_vis);
    free(g_q);
    cap = N;
    g_adj = malloc(sizeof(int) * (size_t)N * MAXD);
    g_cnt = malloc(sizeof(int) * (size_t)N);
    g_vis = calloc((size_t)N, sizeof(int));
    g_q = malloc(sizeof(int) * (size_t)N);
    if (!g_adj || !g_cnt || !g_vis || !g_q) {
        fprintf(stderr, "out of memory\n");
        exit(1);
    }
    g_stamp = 0;
}

static int cost_of(const Cfg *c) {
    int K = c->K, G = GG, N = 2 * K * G;
    for (int v = 0; v < N; v++) g_cnt[v] = 0;
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = c->P[l][i], s = c->S[l][i];
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                int b = (K + j) * G + MT[g * G + s];
                g_adj[a * MAXD + g_cnt[a]++] = b;
                g_adj[b * MAXD + g_cnt[b]++] = a;
            }
        }
    }
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < Dd; l1++)
            for (int l2 = l1 + 1; l2 < Dd; l2++)
                if (c->P[l1][i] == c->P[l2][i] && c->S[l1][i] == c->S[l2][i])
                    dup++;

    long unreached = 0;
    for (int r = 0; r < 2 * K; r++) {
        int src = r * G;
        g_stamp++;
        int head = 0, tail = 0;
        g_vis[src] = g_stamp;
        g_q[tail++] = src;
        for (int lvl = 0; lvl < DD; lvl++) {
            int end = tail;
            if (head == end) break;
            while (head < end) {
                int u = g_q[head++];
                for (int t = 0; t < Dd; t++) {
                    int v = g_adj[u * MAXD + t];
                    if (g_vis[v] != g_stamp) {
                        g_vis[v] = g_stamp;
                        g_q[tail++] = v;
                    }
                }
            }
        }
        unreached += N - tail;
    }
    return (int)unreached + PEN * dup;
}

static void random_cfg(Cfg *c) {
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < c->K; i++) c->P[l][i] = i;
        for (int i = c->K - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = c->P[l][i];
            c->P[l][i] = c->P[l][j];
            c->P[l][j] = t;
        }
        for (int i = 0; i < c->K; i++) c->S[l][i] = rint_(GG);
    }
}

static int anneal(Cfg *c, long iters, double T0) {
    int cost = cost_of(c);
    int bestc = cost;
    Cfg bc = *c;
    for (long t = 0; t < iters && cost != 0; t++) {
        if ((t & 255) == 0 && now_s() > deadline) break;
        double temp = T0 * (1.0 - (double)t / (double)iters) + 0.02;
        int l = rint_(Dd);
        int i = rint_(c->K);
        int kind = (c->K >= 2 && rint_(4) == 0);
        int old_s = 0, i2 = 0;
        if (kind) {
            i2 = rint_(c->K - 1);
            if (i2 >= i) i2++;
            int tmp = c->P[l][i];
            c->P[l][i] = c->P[l][i2];
            c->P[l][i2] = tmp;
        } else {
            old_s = c->S[l][i];
            c->S[l][i] = rint_(GG);
        }
        int c2 = cost_of(c);
        if (c2 <= cost || rdbl() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            if (cost < bestc) {
                bestc = cost;
                bc = *c;
            }
        } else {
            if (kind) {
                int tmp = c->P[l][i];
                c->P[l][i] = c->P[l][i2];
                c->P[l][i2] = tmp;
            } else {
                c->S[l][i] = old_s;
            }
        }
    }
    *c = bc;
    return bestc;
}

static int polish(Cfg *c) {
    int cost = cost_of(c);
    int improved = 1;
    while (improved && cost != 0) {
        improved = 0;
        for (int l = 0; l < Dd && cost != 0; l++) {
            for (int i = 0; i < c->K; i++) {
                if (now_s() > deadline) return cost;
                int old = c->S[l][i];
                int bestv = old, bestc = cost;
                for (int s = 0; s < GG; s++) {
                    if (s == old) continue;
                    c->S[l][i] = s;
                    int c2 = cost_of(c);
                    if (c2 < bestc) {
                        bestc = c2;
                        bestv = s;
                    }
                }
                c->S[l][i] = bestv;
                if (bestv != old) {
                    cost = bestc;
                    improved = 1;
                    if (cost == 0) break;
                }
            }
        }
    }
    return cost;
}

int main(int argc, char **argv) {
    double t0 = now_s();
    Dd = argc > 1 ? atoi(argv[1]) : 3;
    DD = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;
    int min_n = argc > 5 ? atoi(argv[5]) : 0;
    KFIX = argc > 6 ? atoi(argv[6]) : 1;

    if (Dd < 1 || Dd > MAXD || DD < 1 || KFIX < 1 || KFIX > MAXK - 1) {
        printf("0 0\n");
        return 0;
    }

    int m = 0;
    if (scanf("%d %d", &GG, &m) != 2 || GG < 1 || GG > 2000 || m != GG * GG) {
        printf("0 0\n");
        return 0;
    }
    MT = malloc(sizeof(int) * (size_t)m);
    if (!MT) {
        printf("0 0\n");
        return 0;
    }
    for (int t = 0; t < m; t++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) {
            printf("0 0\n");
            return 0;
        }
        if (u < 0 || u >= m || v < 0 || v >= GG) {
            printf("0 0\n");
            return 0;
        }
        MT[u] = v;
    }

    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 4; w++) rnd();

    deadline = t0 + tl;
    int K = KFIX;
    int N = 2 * K * GG;
    if (N <= min_n) {
        printf("0 0\n");
        return 0;
    }
    ensure_cap(N);

    Cfg cur;
    memset(&cur, 0, sizeof(cur));
    cur.K = K;
    int found = 0;
    while (now_s() < deadline) {
        random_cfg(&cur);
        int c = anneal(&cur, ITERS, 1.5);
        if (c > 0 && c <= POLISH_T) c = polish(&cur);
        if (c == 0 && cost_of(&cur) == 0) {
            found = 1;
            break;
        }
    }
    if (!found) {
        printf("0 0\n");
        return 0;
    }

    int G = GG;
    printf("%d %d\n", 2 * K * G, Dd * K * G);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = cur.P[l][i], s = cur.S[l][i];
            for (int g = 0; g < G; g++) {
                printf("%d %d\n", i * G + g, (K + j) * G + MT[g * G + s]);
            }
        }
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions, then group-lift search in C, with a
# valid fallback always available.
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

    # Group-lift search: sample orders in a window above the best known order,
    # build a multiplication table (AGL(1,q) or semidirect product), and let C
    # search for a valid lift of that group.
    if d >= 3 and D >= 3 and d <= 60:
        moore = lib.moore_bound(d, D)
        lo0 = max(best_n + 1, int(0.36 * moore))
        hi0 = max(lo0 + 1, int(0.5 * moore))
        rng = random.Random(seed * 1000003 + 17 * d + D)
        tries = 0
        while True:
            remaining = deadline - time.monotonic()
            if remaining < 2.5:
                break
            budget = min(10.0, max(1.5, remaining / 4.0), remaining - 1.5)
            if budget < 1.0:
                break
            K = 1 if rng.random() < 0.7 else 2
            lo = max(lo0, best_n + 1)
            hi = max(hi0, lo + 1)
            N = lo + int((hi - lo) * rng.random() ** 2)
            G = N // (2 * K)
            if 2 * K * G <= best_n:
                G += 1
            tries += 1
            if G < 2 or G > 1500:
                continue
            T = _group_table(G, rng)
            pairs = list(zip(range(G * G), T.ravel().tolist()))
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed * 7919 + tries, f"{budget:.2f}", best_n, K],
                                stdin_graph=(G, pairs), timeout=budget + 6.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
