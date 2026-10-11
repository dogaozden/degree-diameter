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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# C engine: simulated annealing over bi-Cayley lifts with a WIDE, varied
# family of base sizes (1..4 per side) and semidirect groups Z_m x|_r Z_k.
#
# Vertices: A_{i,g} = i*G+g, B_{j,h} = (B+j)*G+h, dart (l, i) joins
# A_{i,g} to B_{P[l][i], g*S[l][i]}. Each P[l] is a permutation, so every
# vertex has degree exactly Dd. Cost = (unreached pairs from the 2B base
# representatives within DD steps) + PEN * (duplicate darts).
# Cost 0 means a valid graph. The search anneals on the raw cost and then
# finishes near-misses with a best-improvement sweep over single dart values.
# Each accepted graph raises the lower bound for the next group sample.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define MAXD 64
#define MAXB 4
#define MAXGG 6000
#define PEN 3
#define ATT_ITERS 30000L

typedef struct {
    int B, G;
    int P[MAXD][MAXB];
    int S[MAXD][MAXB];
} Cfg;

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int n) { return (int)(rnd64() % (uint64_t)n); }

static double urand(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int Dd = 3, DD = 3;
static int GM = 1, GK = 1, GG = 1;
static long long gpow[64];
static double deadline = 0.0;

static void set_group(int m, int k, int r) {
    long long p = 1 % m;
    GM = m;
    GK = k;
    GG = m * k;
    for (int b = 0; b < k; b++) {
        gpow[b] = p;
        p = (p * r) % m;
    }
}

/* Semidirect product: (a,b)*(c,d) = (a + r^b c, b + d), element coded a*GK+b. */
static int gmul(int x, int y) {
    int a = x / GK, b = x % GK;
    int c = y / GK, d = y % GK;
    long long t = ((long long)a + gpow[b] * (long long)c) % GM;
    return (int)(t * GK + (b + d) % GK);
}

static int capN = 0;
static int *adj = NULL, *dcnt = NULL, *vis = NULL, *qu = NULL;
static int vstamp = 0;

static void ensure_cap(int N) {
    if (N <= capN) return;
    free(adj);
    free(dcnt);
    free(vis);
    free(qu);
    capN = N;
    adj = malloc(sizeof(int) * (size_t)N * (size_t)Dd);
    dcnt = malloc(sizeof(int) * (size_t)N);
    vis = calloc((size_t)N, sizeof(int));
    qu = malloc(sizeof(int) * (size_t)N);
    if (!adj || !dcnt || !vis || !qu) {
        fprintf(stderr, "out of memory\n");
        exit(1);
    }
    vstamp = 0;
}

static void add_edge(int a, int b) {
    if (dcnt[a] < Dd) adj[(size_t)a * Dd + dcnt[a]++] = b;
    if (dcnt[b] < Dd) adj[(size_t)b * Dd + dcnt[b]++] = a;
}

/* Returns raw + PEN * dup. Cost 0 means a valid simple bipartite graph. */
static long long evalcost(const Cfg *c) {
    int B = c->B, G = c->G, N = 2 * B * G;
    ensure_cap(N);
    memset(dcnt, 0, sizeof(int) * (size_t)N);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < B; i++) {
            int j = c->P[l][i], s = c->S[l][i];
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                int b = (B + j) * G + gmul(g, s);
                add_edge(a, b);
            }
        }
    }
    for (int v = 0; v < N; v++)
        while (dcnt[v] < Dd) adj[(size_t)v * Dd + dcnt[v]++] = v;

    int dup = 0;
    for (int i = 0; i < B; i++)
        for (int l1 = 0; l1 < Dd; l1++)
            for (int l2 = l1 + 1; l2 < Dd; l2++)
                if (c->P[l1][i] == c->P[l2][i] && c->S[l1][i] == c->S[l2][i])
                    dup++;

    long long raw = 0;
    for (int r = 0; r < 2 * B; r++) {
        int src = r * G;
        if (vstamp > 0x7ffffff0) {
            memset(vis, 0, sizeof(int) * (size_t)capN);
            vstamp = 0;
        }
        vstamp++;
        int head = 0, tail = 0;
        vis[src] = vstamp;
        qu[tail++] = src;
        for (int lvl = 0; lvl < DD && head < tail; lvl++) {
            int end = tail;
            while (head < end) {
                int u = qu[head++];
                for (int t = 0; t < Dd; t++) {
                    int v = adj[(size_t)u * Dd + t];
                    if (vis[v] != vstamp) {
                        vis[v] = vstamp;
                        qu[tail++] = v;
                    }
                }
            }
        }
        raw += (long long)(N - tail);
    }
    return raw + (long long)PEN * (long long)dup;
}

static void random_cfg(Cfg *c) {
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < c->B; i++) c->P[l][i] = i;
        for (int i = c->B - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = c->P[l][i];
            c->P[l][i] = c->P[l][j];
            c->P[l][j] = t;
        }
        for (int i = 0; i < c->B; i++) c->S[l][i] = rint_(GG);
    }
}

/* Simulated annealing with geometric cooling from T0 to T1. Leaves *cur at
   the best state seen and returns its cost. */
static long long run_attempt(Cfg *cur, long iters, double T0, double T1) {
    long long cost = evalcost(cur);
    Cfg best = *cur;
    long long bestc = cost;
    for (long t = 0; t < iters && bestc > 0; t++) {
        if ((t & 255) == 0 && now_s() > deadline) break;
        double T = T0 * pow(T1 / T0, (double)t / (double)iters);
        int l = rint_(Dd);
        int i = rint_(cur->B);
        int doswap = (cur->B >= 2 && rint_(3) == 0);
        int old = 0, i2 = 0;
        if (doswap) {
            i2 = rint_(cur->B - 1);
            if (i2 >= i) i2++;
            int tmp = cur->P[l][i];
            cur->P[l][i] = cur->P[l][i2];
            cur->P[l][i2] = tmp;
        } else {
            old = cur->S[l][i];
            cur->S[l][i] = rint_(GG);
        }
        long long nc = evalcost(cur);
        long long delta = nc - cost;
        if (delta <= 0 || urand() < exp(-(double)delta / T)) {
            cost = nc;
            if (cost < bestc) {
                bestc = cost;
                best = *cur;
            }
        } else {
            if (doswap) {
                int tmp = cur->P[l][i];
                cur->P[l][i] = cur->P[l][i2];
                cur->P[l][i2] = tmp;
            } else {
                cur->S[l][i] = old;
            }
        }
    }
    *cur = best;
    return bestc;
}

/* Best-improvement sweeps over every single dart value. */
static long long sweep(Cfg *c, long long cost) {
    int improved = 1;
    while (improved && cost > 0) {
        improved = 0;
        for (int l = 0; l < Dd && cost > 0; l++) {
            for (int i = 0; i < c->B; i++) {
                if (now_s() > deadline) return cost;
                int old = c->S[l][i];
                int bv = old;
                long long bc = cost;
                for (int s = 0; s < GG; s++) {
                    if (s == old) continue;
                    c->S[l][i] = s;
                    long long c2 = evalcost(c);
                    if (c2 < bc) {
                        bc = c2;
                        bv = s;
                    }
                }
                c->S[l][i] = bv;
                if (bv != old) {
                    cost = bc;
                    improved = 1;
                    if (cost == 0) break;
                }
            }
        }
    }
    return cost;
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

static const int KF[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18,
                         20, 21, 24, 27, 28, 30, 32, 36, 40, 42, 48};
#define NKF ((int)(sizeof(KF) / sizeof(KF[0])))

/* Pick a group of order m*k in [lo, lo+span] with k from KF and a random r
   satisfying r^k = 1 mod m (r = 1 gives the direct product Z_m x Z_k). */
static int sample_group(long long lo, long long span, int *oM, int *oK, int *oR) {
    for (int tries = 0; tries < 60; tries++) {
        int k = KF[rint_(NKF)];
        long long mmin = (lo + k - 1) / k;
        if (mmin < 2) mmin = 2;
        long long mmax = (lo + span) / k;
        if (mmax < mmin) continue;
        long long m = mmin + (long long)rint_((int)(mmax - mmin + 1));
        if (m * k > MAXGG) continue;
        int r = 1;
        if (k > 1 && m > 2) {
            for (int t = 0; t < 300; t++) {
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
        return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    Dd = argc > 1 ? atoi(argv[1]) : 3;
    DD = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;
    long long min_n = argc > 5 ? atoll(argv[5]) : 0;

    if (Dd < 1 || Dd > MAXD || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 8; w++) rnd64();

    double t0 = now_s();
    deadline = t0 + tl;
    long long best_n = min_n;
    int have = 0;
    int bM = 1, bK = 1, bR = 1;
    Cfg best_cfg;
    memset(&best_cfg, 0, sizeof(best_cfg));

    while (now_s() < deadline) {
        int roll = rint_(100);
        int B = roll < 35 ? 1 : (roll < 70 ? 2 : (roll < 90 ? 3 : 4));
        long long lo = best_n / (2LL * B) + 1;
        if (lo < 2) lo = 2;
        long long span = lo / 16 + 6;
        int M, Kk, R;
        if (!sample_group(lo, span, &M, &Kk, &R)) continue;
        set_group(M, Kk, R);
        if (GG > MAXGG) continue;
        long long N = 2LL * B * GG;
        if (N <= best_n) continue;

        Cfg cur;
        memset(&cur, 0, sizeof(cur));
        cur.B = B;
        cur.G = GG;
        random_cfg(&cur);
        long long c = run_attempt(&cur, ATT_ITERS, 3.0, 0.15);
        if (c > 0 && c <= 10 && now_s() < deadline) c = sweep(&cur, c);
        if (c == 0) {
            best_n = N;
            best_cfg = cur;
            bM = M;
            bK = Kk;
            bR = R;
            have = 1;
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    set_group(bM, bK, bR);
    int B = best_cfg.B, G = best_cfg.G;
    long n = 2L * B * G;
    long m = (long)Dd * B * G;
    printf("%ld %ld\n", n, m);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < B; i++) {
            int j = best_cfg.P[l][i], s = best_cfg.S[l][i];
            for (int g = 0; g < G; g++) {
                printf("%d %d\n", i * G + g, (B + j) * G + gmul(g, s));
            }
        }
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions first, then the C search, always with a
# valid fallback.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(3.0, min(0.85 * time_limit, time_limit - 6.0))

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions.
    if D >= 3:
        try:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
        except Exception:
            pass
        if D == 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
            return best
        if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

    if D == 4 and time.monotonic() < deadline:
        try:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])
                if d - 1 <= 9 and lib.is_prime_power(d - 1):
                    return best
        except Exception:
            pass

    # Annealing over bi-Cayley lifts in C, with the best order so far as the bound.
    if d >= 3 and D >= 3:
        c_budget = deadline - time.monotonic() - 2.0
        if c_budget >= 3.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{c_budget:.2f}", best_n],
                                timeout=time_limit - 4.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
