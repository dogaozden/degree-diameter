import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact baselines (safe fallbacks, kept from the parent).
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
# C engine: simulated annealing over bi-Cayley voltage graphs on semidirect
# products Z_M x| Z_k with K = 1 or 2 base vertices per side. Each candidate
# group gets a fresh annealing run of a few seconds; the cost is the number of
# (representative, vertex) pairs not reached within DD steps, plus a duplicate
# penalty. Cost 0 is a valid graph. Larger groups are tried after each success.
#
# Vertices: A_{i,g} = i*G+g, B_{j,h} = (K+j)*G+h. Dart l at base vertex i joins
# A_{i,g} to B_{P[l][i], g*S[l][i]}. Left multiplication is an automorphism, so
# one representative per side class suffices for the distance check.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 16
#define MAXK 2
#define MAXGG 2600
#define PEN 5

typedef struct {
    int P[MAXD][MAXK];
    int S[MAXD][MAXK];
} Cfg;

static int Dd = 7, DD = 5, K = 1, GG = 1, GM = 1, GK = 1;
static int gpow[256];
static int *MT = NULL;
static long capMT = 0;
static int *adjv = NULL, *cntv = NULL, *visv = NULL, *qv = NULL;
static int capN = 0;
static int stamp_ = 0;
static double deadline = 0.0;
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

static int gmul_f(int x, int y) {
    int a = x / GK, b = x % GK;
    int c = y / GK, d = y % GK;
    long long t = ((long long)a + (long long)gpow[b] * (long long)c) % GM;
    return (int)t * GK + (b + d) % GK;
}

static void set_group(int m, int k, int r) {
    GM = m;
    GK = k;
    GG = m * k;
    long long p = 1 % m;
    for (int b = 0; b < k; b++) {
        gpow[b] = (int)p;
        p = (p * r) % m;
    }
    long need = (long)GG * (long)GG;
    if (!MT || capMT < need) {
        free(MT);
        MT = malloc(sizeof(int) * (size_t)need);
        if (!MT) {
            fprintf(stderr, "out of memory\n");
            exit(1);
        }
        capMT = need;
    }
    for (int x = 0; x < GG; x++)
        for (int y = 0; y < GG; y++)
            MT[(size_t)x * GG + y] = gmul_f(x, y);
}

static void ensure_cap(int N) {
    if (N <= capN) return;
    free(adjv);
    free(cntv);
    free(visv);
    free(qv);
    adjv = malloc(sizeof(int) * (size_t)N * (size_t)Dd);
    cntv = malloc(sizeof(int) * (size_t)N);
    visv = calloc((size_t)N, sizeof(int));
    qv = malloc(sizeof(int) * (size_t)N);
    if (!adjv || !cntv || !visv || !qv) {
        fprintf(stderr, "out of memory\n");
        exit(1);
    }
    capN = N;
    stamp_ = 0;
}

/* Cost = unreached (representative, vertex) pairs within DD steps + PEN * duplicate dart pairs. */
static long long eval(const Cfg *c, int *dupo) {
    int G = GG;
    int N = 2 * K * G;
    ensure_cap(N);
    memset(cntv, 0, sizeof(int) * (size_t)N);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = c->P[l][i], s = c->S[l][i];
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                int b = (K + j) * G + MT[(size_t)g * G + s];
                adjv[a * Dd + cntv[a]++] = b;
                adjv[b * Dd + cntv[b]++] = a;
            }
        }
    }
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < Dd; l1++)
            for (int l2 = l1 + 1; l2 < Dd; l2++)
                if (c->P[l1][i] == c->P[l2][i] && c->S[l1][i] == c->S[l2][i])
                    dup++;
    *dupo = dup;

    long long unr = 0;
    for (int r = 0; r < 2 * K; r++) {
        stamp_++;
        int head = 0, tail = 0;
        int src = r * G;
        visv[src] = stamp_;
        qv[tail++] = src;
        for (int lvl = 0; lvl < DD; lvl++) {
            int end = tail;
            if (head == end) break;
            while (head < end) {
                int u = qv[head++];
                for (int t = 0; t < Dd; t++) {
                    int v = adjv[u * Dd + t];
                    if (visv[v] != stamp_) {
                        visv[v] = stamp_;
                        qv[tail++] = v;
                    }
                }
            }
        }
        unr += (long long)(N - tail);
    }
    return unr + (long long)PEN * (long long)dup;
}

static void random_cfg(Cfg *c) {
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

/* Simulated annealing for tlen seconds. Returns best cost; *best holds that state. */
static long long anneal(const Cfg *start, double tlen, Cfg *best) {
    Cfg cur = *start;
    int dd = 0;
    long long cc = eval(&cur, &dd);
    long long bc = cc;
    *best = cur;
    double t0 = now_s();
    const double T0 = 6.0, T1 = 0.2;
    double T = T0;
    for (long it = 0; cc > 0; it++) {
        if ((it & 31) == 0) {
            double now = now_s();
            double el = now - t0;
            if (el >= tlen || now >= deadline) break;
            double frac = el / tlen;
            T = T0 * pow(T1 / T0, frac);
        }
        int l = rint_(Dd), i = rint_(K);
        int kind = (K >= 2 && rint_(3) == 0);
        int i2 = 0, olds = 0, t;
        if (kind) {
            i2 = rint_(K - 1);
            if (i2 >= i) i2++;
            t = cur.P[l][i];
            cur.P[l][i] = cur.P[l][i2];
            cur.P[l][i2] = t;
        } else {
            olds = cur.S[l][i];
            cur.S[l][i] = rint_(GG);
        }
        long long nc = eval(&cur, &dd);
        if (nc <= cc || rdbl() < exp(-(double)(nc - cc) / T)) {
            cc = nc;
            if (cc < bc) {
                bc = cc;
                *best = cur;
            }
        } else {
            if (kind) {
                t = cur.P[l][i];
                cur.P[l][i] = cur.P[l][i2];
                cur.P[l][i2] = t;
            } else {
                cur.S[l][i] = olds;
            }
        }
    }
    return bc;
}

int main(int argc, char **argv) {
    Dd = argc > 1 ? atoi(argv[1]) : 3;
    DD = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;
    int best_n = argc > 5 ? atoi(argv[5]) : 0;
    int start_n = argc > 6 ? atoi(argv[6]) : 0;

    if (Dd < 1 || Dd > MAXD || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 4; w++) rnd();

    double t0 = now_s();
    deadline = t0 + tl;

    int have = 0;
    Cfg bestcfg;
    memset(&bestcfg, 0, sizeof(bestcfg));
    int bK = 1, bM = 1, bk = 1, bR = 1;

    static const int KF[] = {1, 1, 1, 2, 3, 4, 6, 7, 7, 9, 12, 14, 21, 27};
    int nkf = (int)(sizeof(KF) / sizeof(KF[0]));

    while (now_s() < deadline - 0.5) {
        K = (rint_(100) < 70) ? 1 : 2;
        int ref = best_n > start_n ? best_n : start_n;
        long long Gmin = ref / (2 * K) + 1;
        long long span = Gmin / 40 + 3;
        long long G = Gmin + rint_((int)span);
        int k = KF[rint_(nkf)];
        if ((long long)k > G) k = 1;
        long long Mll = (G + k - 1) / k;
        if (Mll < 2) Mll = 2;
        int M = (int)Mll;
        int r = 1;
        if (k > 1 && M > 2) {
            for (int t = 0; t < 200; t++) {
                long long c = 2 + (long long)rint_(M - 2);
                if (gcdll(c, M) == 1 && powmod(c, k, M) == 1 % M) {
                    r = (int)c;
                    break;
                }
            }
        }
        if ((long long)M * k > MAXGG) continue;
        set_group(M, k, r);
        int N = 2 * K * GG;
        if (N <= best_n) continue;
        ensure_cap(N);

        double rem = deadline - now_s();
        if (rem < 0.5) break;
        double chunk = rem / 3.0;
        if (chunk > 10.0) chunk = 10.0;
        if (chunk < 3.0) chunk = 3.0;
        if (chunk > rem) chunk = rem;

        Cfg cur;
        random_cfg(&cur);
        Cfg bc;
        long long cost = anneal(&cur, chunk, &bc);
        if (cost == 0) {
            best_n = N;
            bestcfg = bc;
            bK = K;
            bM = M;
            bk = k;
            bR = r;
            have = 1;
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    K = bK;
    set_group(bM, bk, bR);
    int G = GG;
    int n = 2 * K * G;
    long m = (long)Dd * K * G;
    printf("%d %ld\n", n, m);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = bestcfg.P[l][i], s = bestcfg.S[l][i];
            for (int g = 0; g < G; g++) {
                printf("%d %d\n", i * G + g, (K + j) * G + MT[(size_t)g * G + s]);
            }
        }
    }
    return 0;
}
'''


# Known record orders used only to choose where the C search starts sampling.
RECORD_START = {(7, 5): 1120}


# ----------------------------------------------------------------------------
# Python glue: exact constructions first, then the C annealer.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(3.0, min(0.88 * time_limit, time_limit - 5.0))

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

    # Bi-Cayley annealing in C, seeded with the best known order.
    if d >= 3 and D >= 3:
        c_budget = deadline - time.monotonic() - 1.0
        if c_budget >= 2.0:
            start_n = max(best_n, RECORD_START.get((d, D), 0))
            try:
                out = lib.run_c(C_SOURCE,
                                [d, D, seed, f"{c_budget:.2f}", best_n, start_n],
                                timeout=time_limit - 3.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
