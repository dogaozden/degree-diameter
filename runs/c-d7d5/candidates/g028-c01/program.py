import itertools
import time

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
    """W(q) for the largest small prime power q with q + 1 <= d (kept small for Python speed)."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# C engine: bi-Cayley lifts over semidirect products Z_m x| Z_k, searched by
# SIMULATED ANNEALING on the number of unreached (rep, vertex) pairs within DD
# steps, plus a duplicate-dart penalty. This replaces the earlier breakout /
# near-miss ILS. Cost 0 means a valid graph.
#
# Vertices: A_{i,g} = i*G+g, B_{j,h} = (K+j)*G+h. Layer l, base vertex i: dart
# joins A_{i,g} to B_{P[l][i], g*S[l][i]}. Each P[l] is a permutation, so every
# vertex has degree Dd. Left translation is an automorphism, so BFS from one
# representative per base vertex (2K sources) certifies the diameter.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 16
#define MAXK 3
#define MAXG 8000
#define MAXN (2 * MAXK * MAXG)
#define DUP_PEN 1000
#define ITERS 100000L
#define T_HOT 2.0
#define T_COLD 0.05

typedef struct {
    int K;
    int P[MAXD][MAXK];
    int S[MAXD][MAXK];
} Cfg;

static int Dd = 3, DD = 3;
static double deadline = 0.0;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }

static double rnd01(void) {
    return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0);
}

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int GM = 1, GK = 1, GG = 1;
static int gpow[256];

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

/* Element (a,b) coded as a*GK+b; (a,b)*(c,d) = (a + r^b c, b + d). */
static int gmul(int x, int y) {
    int a = x / GK, b = x % GK;
    int c = y / GK, d = y % GK;
    long long t = ((long long)a + (long long)gpow[b] * (long long)c) % GM;
    return (int)t * GK + (b + d) % GK;
}

static int adj[MAXN * MAXD];
static int vis[MAXN];
static int qbuf[MAXN];
static int stamp = 0;
static Cfg cur_best_global;
static Cfg best_cfg;

static void build_adj(const Cfg *c, int *dups) {
    int K = c->K;
    int G = GG;
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = c->P[l][i], s = c->S[l][i];
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                int b = (K + j) * G + gmul(g, s);
                adj[a * Dd + l] = b;
                adj[b * Dd + l] = a;
            }
        }
    }
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < Dd; l1++)
            for (int l2 = l1 + 1; l2 < Dd; l2++)
                if (c->P[l1][i] == c->P[l2][i] && c->S[l1][i] == c->S[l2][i])
                    dup++;
    *dups = dup;
}

static long bfs_unreached(int src, int N) {
    stamp++;
    int head = 0, tail = 0;
    vis[src] = stamp;
    qbuf[tail++] = src;
    for (int lvl = 0; lvl < DD; lvl++) {
        int end = tail;
        if (head == end) break;
        while (head < end) {
            int u = qbuf[head++];
            const int *au = adj + (size_t)u * Dd;
            for (int t = 0; t < Dd; t++) {
                int v = au[t];
                if (vis[v] != stamp) {
                    vis[v] = stamp;
                    qbuf[tail++] = v;
                }
            }
        }
    }
    return (long)(N - tail);
}

static long evalc(const Cfg *c) {
    int K = c->K;
    int N = 2 * K * GG;
    int dups = 0;
    build_adj(c, &dups);
    long unr = 0;
    for (int r = 0; r < 2 * K; r++) unr += bfs_unreached(r * GG, N);
    return unr + (long)DUP_PEN * (long)dups;
}

static void random_cfg(Cfg *c, int K) {
    c->K = K;
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) c->P[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = c->P[l][i];
            c->P[l][i] = c->P[l][j];
            c->P[l][j] = t;
        }
        for (int i = 0; i < K; i++) c->S[l][i] = rint_(GG);
    }
}

/* Simulated annealing with geometric cooling from T_HOT to T_COLD.
   Moves: re-draw one voltage, or swap two base targets within a layer.
   Leaves the best state seen in *best. */
static long anneal(Cfg *c, long iters, Cfg *best, long *bestcost) {
    int K = c->K;
    long cc = evalc(c);
    long bc = cc;
    *best = *c;
    double lr = log(T_COLD / T_HOT);
    for (long t = 0; t < iters && bc > 0; t++) {
        if ((t & 255) == 0 && now_s() > deadline) break;
        double T = T_HOT * exp(lr * (double)t / (double)iters);
        int l = rint_(Dd), i = rint_(K);
        int swapped = 0, i2 = 0, old = 0;
        if (K >= 2 && rint_(4) == 0) {
            i2 = rint_(K - 1);
            if (i2 >= i) i2++;
            int tmp = c->P[l][i];
            c->P[l][i] = c->P[l][i2];
            c->P[l][i2] = tmp;
            swapped = 1;
        } else {
            old = c->S[l][i];
            c->S[l][i] = rint_(GG);
        }
        long nc = evalc(c);
        int accept = (nc <= cc) || (rnd01() < exp((double)(cc - nc) / T));
        if (accept) {
            cc = nc;
            if (cc < bc) {
                bc = cc;
                *best = *c;
            }
        } else {
            if (swapped) {
                int tmp = c->P[l][i];
                c->P[l][i] = c->P[l][i2];
                c->P[l][i2] = tmp;
            } else {
                c->S[l][i] = old;
            }
        }
    }
    *bestcost = bc;
    return bc;
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

/* Pick k, then m = ceil(target/k) and r with r^k = 1 mod m (r = 1 otherwise,
   which is the direct product Z_m x Z_k). */
static void sample_group(long long target, int *om, int *ok, int *orr) {
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
    *om = (int)m;
    *ok = k;
    *orr = r;
}

int main(int argc, char **argv) {
    Dd = argc > 1 ? atoi(argv[1]) : 3;
    DD = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;
    long min_n = argc > 5 ? atol(argv[5]) : 0;

    if (Dd < 1 || Dd > MAXD || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 4; w++) rnd();

    double t0 = now_s();
    deadline = t0 + tl;

    long best_n = min_n;
    int have = 0;
    int bM = 1, bK = 1, bR = 1;
    int fails = 0;
    memset(&best_cfg, 0, sizeof(best_cfg));

    static Cfg cur, run_best;

    while (now_s() < deadline) {
        int nb = (rint_(100) < 70) ? 1 : ((rint_(100) < 80) ? 2 : 3);
        long long g0 = best_n / (2LL * nb) + 1;
        long long span = g0 / 20 + 4 + (long long)(fails / 30) * (g0 / 60 + 1);
        if (span > g0 / 4 + 6) span = g0 / 4 + 6;
        long long g = g0 + (long long)rint_((int)span);
        if (g > MAXG) {
            fails++;
            continue;
        }
        int gm, gk, gr;
        sample_group(g, &gm, &gk, &gr);
        set_group(gm, gk, gr);
        if (GG > MAXG) {
            fails++;
            continue;
        }
        long N = 2L * nb * GG;
        if (N <= best_n) {
            fails++;
            continue;
        }
        random_cfg(&cur, nb);
        long bcost = 0;
        anneal(&cur, ITERS, &run_best, &bcost);
        if (bcost == 0) {
            best_n = N;
            best_cfg = run_best;
            bM = gm;
            bK = gk;
            bR = gr;
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
    set_group(bM, bK, bR);
    if (evalc(&best_cfg) != 0) {
        printf("0 0\n");
        return 0;
    }
    int K = best_cfg.K;
    int G = GG;
    int n = 2 * K * G;
    long m = (long)Dd * K * G;
    printf("%d %ld\n", n, m);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = best_cfg.P[l][i], s = best_cfg.S[l][i];
            for (int g = 0; g < G; g++) {
                printf("%d %d\n", i * G + g, (K + j) * G + gmul(g, s));
            }
        }
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions first, then the annealing engine. Every
# candidate is checked with lib.is_valid before it can replace the fallback.
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

    if D == 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 7 and lib.is_prime_power(d - 1):
                return best

    # Annealing search over bi-Cayley lifts, seeded with the best order so far.
    if d >= 3 and D >= 3:
        c_budget = deadline - time.monotonic() - 1.5
        if c_budget >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{c_budget:.2f}", best_n],
                                timeout=time_limit - 2.5)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
