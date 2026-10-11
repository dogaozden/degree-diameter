import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact constructions (safe baselines).
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
# C engine: simulated annealing over metacyclic group lifts (bi-Cayley type).
#
# Model: K left blocks A_i and K right blocks B_j, each of size G = |Z_m x| Z_k|.
# Layer l (0..d-1) is a perfect matching given by permutation P[l] and labels S[l][i]
# in the group: A_{i,g} ~ B_{P[l][i], g*S[l][i]}. The graph is d-regular bipartite.
#
# Key fact used for speed: left multiplication by a group element is an
# automorphism of every block, so the diameter is <= DD iff a BFS of depth DD
# from A_{i,1} (for each i) and from B_{j,1} (for each j) reaches every vertex.
# Cost = total unreached (root, vertex) pairs + PEN * duplicate darts.
# Cost 0 means a valid graph of order 2*K*G.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 16
#define MAXK 4
#define MAXGG 1600
#define MAXN (2 * MAXK * MAXGG)
#define PEN 1000
#define ATT_ITERS 50000
#define T0 6.0
#define T1 0.3

typedef struct {
    int P[MAXD][MAXK];
    int S[MAXD][MAXK];
} Cfg;

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rnd_int(int n) { return (int)(rnd64() % (uint64_t)n); }

static double rnd_unit(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int Dd = 3, DD = 3, K = 1, GM = 1, GK = 1, GG = 1;
static int gpow[MAXGG];
static int gtab[MAXGG * MAXGG];
static int adj[MAXN * MAXD];
static int cntv[MAXN];
static int vis[MAXN];
static int qbuf[MAXN];
static int stamp = 0;
static int Nn = 0;
static double deadline = 0.0;

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

/* Group Z_m x|_r Z_k, element (a,b) coded as a*k+b, (a,b)(c,d) = (a + r^b c, b + d). */
static void set_group(int m, int k, int r) {
    GM = m;
    GK = k;
    GG = m * k;
    long long p = 1 % m;
    for (int b = 0; b < k; b++) {
        gpow[b] = (int)p;
        p = (p * r) % m;
    }
    for (int x = 0; x < GG; x++) {
        int a = x / GK, b = x % GK;
        for (int y = 0; y < GG; y++) {
            int c = y / GK, d = y % GK;
            long long t = ((long long)a + (long long)gpow[b] * (long long)c) % GM;
            gtab[x * GG + y] = (int)(t * GK + (b + d) % GK);
        }
    }
}

static void sample_group(int target, int *om, int *ok, int *orr) {
    int divs[128], nd = 0;
    for (int dv = 1; dv <= 64 && dv < target; dv++)
        if (target % dv == 0 && target / dv >= 2) divs[nd++] = dv;
    int kk = nd ? divs[rnd_int(nd)] : 1;
    int mm = target / kk;
    int rr = 1;
    if (kk > 1 && mm > 2) {
        for (int t = 0; t < 400; t++) {
            int c = 2 + rnd_int(mm - 2);
            if (gcdll(c, mm) == 1 && powmod(c, kk, mm) == 1 % mm) {
                rr = c;
                break;
            }
        }
    }
    *om = mm;
    *ok = kk;
    *orr = rr;
}

/* Builds adjacency for the current K, GG, Dd; returns number of duplicate darts. */
static int build_adj(const Cfg *c) {
    int N = 2 * K * GG;
    Nn = N;
    for (int v = 0; v < N; v++) cntv[v] = 0;
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = c->P[l][i], s = c->S[l][i];
            for (int g = 0; g < GG; g++) {
                int a = i * GG + g;
                int b = (K + j) * GG + gtab[g * GG + s];
                adj[a * Dd + cntv[a]++] = b;
                adj[b * Dd + cntv[b]++] = a;
            }
        }
    }
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < Dd; l1++)
            for (int l2 = l1 + 1; l2 < Dd; l2++)
                if (c->P[l1][i] == c->P[l2][i] && c->S[l1][i] == c->S[l2][i])
                    dup++;
    return dup;
}

static long long eval_cfg(const Cfg *c) {
    int dup = build_adj(c);
    int N = Nn;
    long long raw = 0;
    for (int r = 0; r < 2 * K; r++) {
        int src = r * GG;
        stamp++;
        int head = 0, tail = 0;
        qbuf[tail++] = src;
        vis[src] = stamp;
        for (int lvl = 0; lvl < DD; lvl++) {
            int end = tail;
            if (head == end) break;
            while (head < end) {
                int u = qbuf[head++];
                const int *au = adj + u * Dd;
                for (int t = 0; t < Dd; t++) {
                    int v = au[t];
                    if (vis[v] != stamp) {
                        vis[v] = stamp;
                        qbuf[tail++] = v;
                    }
                }
            }
        }
        raw += N - tail;
    }
    return raw + (long long)PEN * dup;
}

static void random_cfg(Cfg *c) {
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) c->P[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rnd_int(i + 1);
            int t = c->P[l][i];
            c->P[l][i] = c->P[l][j];
            c->P[l][j] = t;
        }
        for (int i = 0; i < K; i++) c->S[l][i] = rnd_int(GG);
    }
}

/* Simulated annealing on the cost; returns the best cost seen, stores best state. */
static long long anneal(Cfg *c, Cfg *best, long iters) {
    long long cur = eval_cfg(c);
    long long bestc = cur;
    *best = *c;
    for (long t = 0; t < iters && bestc > 0; t++) {
        if ((t & 255) == 0 && now_s() > deadline) break;
        double T = T0 * pow(T1 / T0, (double)t / (double)iters);
        Cfg old = *c;
        int l = rnd_int(Dd), i = rnd_int(K);
        if (K >= 2 && rnd_int(4) == 0) {
            int i2 = rnd_int(K - 1);
            if (i2 >= i) i2++;
            int tmp = c->P[l][i];
            c->P[l][i] = c->P[l][i2];
            c->P[l][i2] = tmp;
        } else {
            c->S[l][i] = rnd_int(GG);
        }
        long long nc = eval_cfg(c);
        long long delta = nc - cur;
        if (delta <= 0 || rnd_unit() < exp(-(double)delta / T)) {
            cur = nc;
            if (cur < bestc) {
                bestc = cur;
                *best = *c;
            }
        } else {
            *c = old;
        }
    }
    return bestc;
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
    for (int w = 0; w < 8; w++) rnd64();
    deadline = now_s() + tl;

    int best_n = min_n;
    int have = 0;
    int fails = 0;
    Cfg best_cfg;
    memset(&best_cfg, 0, sizeof(best_cfg));
    int bK = 1, bM = 1, bKk = 1, bR = 1;

    while (now_s() < deadline) {
        int kc = rnd_int(100);
        int Kc = kc < 60 ? 1 : (kc < 90 ? 2 : 3);
        long long gmin = best_n / (2 * Kc) + 1;
        long long span = 3 + fails / 15;
        if (span > 80) span = 80;
        long long target = gmin + rnd_int((int)span);
        if (target < 2) target = 2;
        if (target > MAXGG) {
            fails++;
            continue;
        }
        K = Kc;
        int m, k, r;
        sample_group((int)target, &m, &k, &r);
        set_group(m, k, r);
        Cfg cur, bc;
        random_cfg(&cur);
        long long c = anneal(&cur, &bc, ATT_ITERS);
        if (c == 0) {
            best_n = 2 * K * GG;
            best_cfg = bc;
            bK = K;
            bM = m;
            bKk = k;
            bR = r;
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
    K = bK;
    set_group(bM, bKk, bR);
    int N = 2 * K * GG;
    long m = (long)Dd * K * GG;
    printf("%d %ld\n", N, m);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = best_cfg.P[l][i], s = best_cfg.S[l][i];
            for (int g = 0; g < GG; g++) {
                printf("%d %d\n", i * GG + g, (K + j) * GG + gtab[g * GG + s]);
            }
        }
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions first, then the C annealer.
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

    # Annealing over metacyclic group lifts, seeded with the best order so far.
    if d >= 3 and D >= 3:
        c_budget = deadline - time.monotonic() - 1.0
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
