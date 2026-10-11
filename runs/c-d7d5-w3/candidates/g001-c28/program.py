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
# C engine: simulated annealing over bi-Cayley graphs on semidirect products
# Z_m x|_r Z_k. Vertices A_{i,g} = i*G+g and B_{j,h} = (K+j)*G+h; dart (l,i)
# joins A_{i,g} to B_{P[l][i], g*S[l][i]}. Left multiplication is an
# automorphism, so one BFS per orbit representative (2K of them) decides the
# diameter. Cost = unreached (representative, vertex) pairs + PEN * duplicate
# darts. Cost 0 means valid. The target order starts at a lower bound from
# the caller and switches to "strictly beat the best found" after the first hit.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define MAXD 16
#define MAXK 3
#define PEN 40
#define MAXG 1600

typedef struct {
    int K;
    int P[MAXD][MAXK];
    int S[MAXD][MAXK];
} Cfg;

static int Dd = 3, DD = 3;
static uint64_t rs = 88172645463325252ULL;
static double deadline = 0.0;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }

static double urand(void) {
    return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0);
}

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static const int KF[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18,
                         20, 21, 24, 27, 28, 30, 32, 36, 40};

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

/* Group Z_m x|_r Z_k, element (a,b) coded as a*k+b. Multiplication table in mt. */
static int GM = 1, GK = 1, GR = 1, GO = 1;
static int gpow[64];
static int *mt = NULL;
static long mt_cap = 0;

static void set_group(int m, int k, int r) {
    GM = m;
    GK = k;
    GR = r;
    GO = m * k;
    long long p = 1 % m;
    for (int b = 0; b < k; b++) {
        gpow[b] = (int)p;
        p = (p * r) % m;
    }
    long need = (long)GO * (long)GO;
    if (need > mt_cap) {
        free(mt);
        mt = malloc(sizeof(int) * (size_t)need);
        if (!mt) {
            fprintf(stderr, "oom\n");
            exit(1);
        }
        mt_cap = need;
    }
    for (int x = 0; x < GO; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < GO; y++) {
            int c = y / k, d = y % k;
            long long t = ((long long)a + (long long)gpow[b] * (long long)c) % m;
            mt[x * GO + y] = (int)(t * k + (b + d) % k);
        }
    }
}

static int *adj = NULL, *ccnt = NULL, *vis = NULL, *qu = NULL;
static int capN = 0, stamp = 0;

static void ensureN(int N) {
    if (N <= capN) return;
    free(adj);
    free(ccnt);
    free(vis);
    free(qu);
    capN = N;
    adj = malloc(sizeof(int) * (size_t)N * MAXD);
    ccnt = malloc(sizeof(int) * (size_t)N);
    vis = calloc((size_t)N, sizeof(int));
    qu = malloc(sizeof(int) * (size_t)N);
    if (!adj || !ccnt || !vis || !qu) {
        fprintf(stderr, "oom\n");
        exit(1);
    }
    stamp = 0;
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
        for (int i = 0; i < K; i++) c->S[l][i] = rint_(GO);
    }
}

static long long eval_cost(const Cfg *c) {
    int K = c->K, G = GO, N = 2 * K * G;
    ensureN(N);
    for (int v = 0; v < N; v++) ccnt[v] = 0;
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = c->P[l][i], s = c->S[l][i];
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                int b = (K + j) * G + mt[g * G + s];
                adj[a * MAXD + ccnt[a]++] = b;
                adj[b * MAXD + ccnt[b]++] = a;
            }
        }
    }
    long long dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < Dd; l1++)
            for (int l2 = l1 + 1; l2 < Dd; l2++)
                if (c->P[l1][i] == c->P[l2][i] && c->S[l1][i] == c->S[l2][i]) dup++;

    long long raw = 0;
    for (int r = 0; r < 2 * K; r++) {
        int src = r * G;
        stamp++;
        int head = 0, tail = 0;
        vis[src] = stamp;
        qu[tail++] = src;
        for (int lvl = 0; lvl < DD; lvl++) {
            int end = tail;
            if (head == end) break;
            while (head < end) {
                int u = qu[head++];
                for (int t = 0; t < Dd; t++) {
                    int v = adj[u * MAXD + t];
                    if (vis[v] != stamp) {
                        vis[v] = stamp;
                        qu[tail++] = v;
                    }
                }
            }
        }
        raw += N - tail;
    }
    return raw + (long long)PEN * dup;
}

/* Simulated annealing from *c. Writes the best configuration to *out and
   returns its cost (0 means a valid graph). */
static long long sa_run(Cfg *c, long iters, Cfg *out) {
    int K = c->K, G = GO;
    long long cc = eval_cost(c);
    long long best = cc;
    Cfg bc = *c;
    const double T0 = 2.0, T1 = 0.1;
    for (long t = 0; t < iters && best > 0; t++) {
        if ((t & 255) == 0 && now_s() > deadline) break;
        double T = T0 * pow(T1 / T0, (double)t / (double)iters);
        int l = rint_(Dd), i = rint_(K);
        int kind = (K >= 2 && rint_(3) == 0);
        int old_s = 0, i2 = 0, tmp;
        if (kind) {
            i2 = rint_(K - 1);
            if (i2 >= i) i2++;
            tmp = c->P[l][i];
            c->P[l][i] = c->P[l][i2];
            c->P[l][i2] = tmp;
        } else {
            old_s = c->S[l][i];
            c->S[l][i] = rint_(G);
        }
        long long nc = eval_cost(c);
        int acc = (nc <= cc) || (urand() < exp((double)(cc - nc) / T));
        if (acc) {
            cc = nc;
            if (cc < best) {
                best = cc;
                bc = *c;
            }
        } else {
            if (kind) {
                tmp = c->P[l][i];
                c->P[l][i] = c->P[l][i2];
                c->P[l][i2] = tmp;
            } else {
                c->S[l][i] = old_s;
            }
        }
    }
    *out = bc;
    return best;
}

int main(int argc, char **argv) {
    Dd = argc > 1 ? atoi(argv[1]) : 3;
    DD = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;
    long lo_target = argc > 5 ? atol(argv[5]) : 100;

    if (Dd < 1 || Dd > MAXD || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 777ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 8; w++) rnd();

    double t0 = now_s();
    deadline = t0 + tl;
    int have = 0;
    long best_n = 0;
    Cfg bestc;
    memset(&bestc, 0, sizeof(bestc));
    int bK = 1, bM = 1, bk = 1, br = 1;
    int nKF = (int)(sizeof(KF) / sizeof(KF[0]));

    while (now_s() < deadline) {
        double el = now_s() - t0;
        long target;
        if (have) target = best_n + 1;
        else if (el > 0.35 * tl) target = (long)(0.8 * (double)lo_target);
        else target = lo_target;
        if (target < 4) target = 4;

        int roll = rint_(100);
        int K = roll < 60 ? 1 : (roll < 85 ? 2 : 3);
        long G_lo = (target + 2L * K - 1) / (2L * K);
        long span = 3 + G_lo / 50;
        long Gt = G_lo + (long)rint_((int)span + 1);
        if (Gt > MAXG) Gt = MAXG - rint_(50);

        int k = KF[rint_(nKF)];
        long m = (Gt + k - 1) / k;
        if (m < 2) m = 2;
        long Gact = m * k;
        if (Gact > MAXG) continue;
        if (2L * K * Gact <= best_n) continue;

        int r = 1;
        if (k > 1 && m > 2) {
            for (int t = 0; t < 200; t++) {
                long long cand = 2 + (long long)rint_((int)(m - 2));
                if (gcdll(cand, m) == 1 && powmod(cand, k, m) == 1 % m) {
                    r = (int)cand;
                    break;
                }
            }
        }

        set_group((int)m, k, r);
        Cfg cur;
        random_cfg(&cur, K);
        Cfg found;
        long long res = sa_run(&cur, 15000, &found);
        if (res == 0) {
            have = 1;
            best_n = 2L * K * Gact;
            bestc = found;
            bK = K;
            bM = (int)m;
            bk = k;
            br = r;
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    set_group(bM, bk, br);
    int K = bestc.K, G = GO;
    int n = 2 * K * G;
    long m = (long)Dd * K * G;
    printf("%d %ld\n", n, m);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = bestc.P[l][i], s = bestc.S[l][i];
            for (int g = 0; g < G; g++) {
                printf("%d %d\n", i * G + g, (K + j) * G + mt[g * G + s]);
            }
        }
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions, cheap algebraic fallbacks, then the C search.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(cand):
        nonlocal best
        if cand is None:
            return
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact constructions.
    if D >= 3:
        consider(_best_pg(d))
        if D == 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
            return best
    if D == 4 and d - 1 >= 2 and d - 1 <= 9 and lib.is_prime_power(d - 1):
        consider(_best_gq(d))
        return best

    # Araujo-Pardo & Lopez graph (diameter 3, so also valid for larger D).
    if D >= 3 and d >= 5 and lib.is_prime_power(d - 2):
        try:
            consider(lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

    # Bold search: simulated annealing over bi-Cayley graphs on semidirect products.
    if D >= 3 and 3 <= d <= 16:
        remaining = time_limit - (time.monotonic() - t0)
        budget = remaining - 7.0
        if budget >= 2.0:
            moore = lib.moore_bound(d, D)
            lo = max(4, int(0.355 * moore))
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", lo],
                                timeout=remaining - 2.0)
                consider(lib.parse_graph_text(out))
            except Exception:
                pass

    # Generalized quadrangle as a late fallback for D >= 4, if time allows.
    if D >= 4 and time_limit - (time.monotonic() - t0) > 10.0:
        try:
            consider(_best_gq(d))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
