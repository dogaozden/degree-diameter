import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact baselines (unchanged from the parent): PG(2,q) and W(q) incidence graphs.
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
# C engine: bi-Cayley lifts over semidirect products Z_m x| Z_k, searched by
# simulated annealing on the raw count of unreached (rep, vertex) pairs.
# This replaces the parent's breakout search with a different move set and
# acceptance rule. Multi-edges from duplicate darts are harmless for distances,
# so they are removed at output time instead of being penalised.
#
# Vertices: A_{i,g} = i*G+g, B_{j,h} = (K+j)*G+h. Layer l, index i gives the
# darts A_{i,g} -- B_{P[l][i], g*S[l][i]}. Each P[l] is a permutation, so every
# vertex has degree exactly Dd before deduplication. Left multiplication is an
# automorphism, so one BFS per part (identity vertex) covers all pairs.
# Adaptive target: aim for orders above the best known; decay the aim toward
# the best valid order when repeated annealing runs fail.
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
#define FAIL_LIMIT 4
#define ITERS 30000

typedef struct {
    int K, G;
    int P[MAXD][MAXK];
    int S[MAXD][MAXK];
} Cfg;

static int Dd = 3, DD = 3;
static int GM = 1, GK = 1, GG = 1;
static int gpow[64];
static double deadline = 0.0;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }

static double unif(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
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
}

/* (a,b)*(c,d) = (a + r^b c, b + d), element (a,b) coded as a*k+b. */
static int gmul(int x, int y) {
    int a = x / GK, b = x % GK;
    int c = y / GK, d = y % GK;
    long long t = ((long long)a + (long long)gpow[b] * (long long)c) % GM;
    return (int)t * GK + (b + d) % GK;
}

static int adj[MAXN * MAXD];
static int cnt[MAXN];
static int vis[MAXN];
static int qu[MAXN];
static int stamp = 0;

/* Raw cost: number of (representative, vertex) pairs not reached within DD steps. */
static long long eval_cfg(const Cfg *c) {
    int K = c->K, G = c->G, N = 2 * K * G;
    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = c->P[l][i], s = c->S[l][i];
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                int b = (K + j) * G + gmul(g, s);
                adj[a * Dd + cnt[a]++] = b;
                adj[b * Dd + cnt[b]++] = a;
            }
        }
    }
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
                    int v = adj[u * Dd + t];
                    if (vis[v] != stamp) {
                        vis[v] = stamp;
                        qu[tail++] = v;
                    }
                }
            }
        }
        raw += N - tail;
    }
    return raw;
}

static void random_cfg(Cfg *c, int K, int G) {
    c->K = K;
    c->G = G;
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) c->P[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = c->P[l][i];
            c->P[l][i] = c->P[l][j];
            c->P[l][j] = t;
        }
        for (int i = 0; i < K; i++) c->S[l][i] = rint_(G);
    }
}

/* Simulated annealing on the raw cost. Returns the best raw cost and stores
   the corresponding configuration in *bc. */
static long long anneal(Cfg *c, long iters, double T0, double T1, Cfg *bc) {
    long long cur = eval_cfg(c);
    long long bestraw = cur;
    *bc = *c;
    for (long t = 0; t < iters && bestraw > 0; t++) {
        if ((t & 63) == 0 && now_s() > deadline) break;
        double T = T0 * pow(T1 / T0, (double)t / (double)iters);
        int K = c->K, G = c->G;
        int l = rint_(Dd), i = rint_(K);
        int kind = (K >= 2 && rint_(10) < 4);
        int i2 = 0, olds = 0;
        if (kind) {
            i2 = rint_(K - 1);
            if (i2 >= i) i2++;
            int tmp = c->P[l][i];
            c->P[l][i] = c->P[l][i2];
            c->P[l][i2] = tmp;
        } else {
            olds = c->S[l][i];
            c->S[l][i] = rint_(G);
        }
        long long nc = eval_cfg(c);
        long long delta = nc - cur;
        if (delta <= 0 || unif() < exp(-(double)delta / T)) {
            cur = nc;
            if (cur < bestraw) {
                bestraw = cur;
                *bc = *c;
            }
        } else {
            if (kind) {
                int tmp = c->P[l][i];
                c->P[l][i] = c->P[l][i2];
                c->P[l][i2] = tmp;
            } else {
                c->S[l][i] = olds;
            }
        }
    }
    return bestraw;
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

static const int KF[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20,
                         24, 28, 30, 32, 36, 40};

/* Random semidirect product Z_m x| Z_k with order m*k >= G (r^k = 1 mod m). */
static void sample_group(long long G, int *oM, int *oK, int *oR) {
    int nk = (int)(sizeof(KF) / sizeof(KF[0]));
    int k = KF[rint_(nk)];
    if (k > G) k = 1;
    long long m = (G + k - 1) / k;
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
    long long min_n = argc > 5 ? atoll(argv[5]) : 0;
    long long aim = argc > 6 ? atoll(argv[6]) : 0;

    if (Dd < 1 || Dd > MAXD || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 4; w++) rnd();

    double t0 = now_s();
    deadline = t0 + tl;

    long long best_n = min_n;
    if (aim < best_n + 1) aim = best_n + 1;
    int have = 0;
    Cfg best_cfg;
    memset(&best_cfg, 0, sizeof(best_cfg));
    int bM = 1, bk = 1, bR = 1;
    int fails = 0;

    while (now_s() < deadline) {
        int K = 1;
        int roll = rint_(100);
        if (roll >= 50) K = (roll < 85) ? 2 : 3;

        long long Gmin = aim / (2 * K) + 1;
        long long span = Gmin / 30 + 2;
        long long G = Gmin + (long long)rint_((int)span);
        long long lowG = best_n / (2 * K) + 1;
        if (G < lowG) G = lowG;
        if (G > MAXG) G = MAXG;

        int M, Kk, R;
        sample_group(G, &M, &Kk, &R);
        set_group(M, Kk, R);
        if (GG > MAXG) continue;

        long long N = 2LL * K * GG;
        if (N <= best_n) continue;

        Cfg cur, bc;
        random_cfg(&cur, K, GG);
        long long raw = anneal(&cur, ITERS, 3.0, 0.1, &bc);

        if (raw == 0) {
            best_n = N;
            best_cfg = bc;
            bM = M;
            bk = Kk;
            bR = R;
            have = 1;
            fails = 0;
            aim = N + 1;
        } else {
            fails++;
            if (fails >= FAIL_LIMIT) {
                fails = 0;
                long long gap = aim - best_n - 1;
                aim = best_n + 1 + gap / 2;
            }
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }

    set_group(bM, bk, bR);
    int K = best_cfg.K, G = best_cfg.G;
    int N = 2 * K * G;
    size_t cap = (size_t)Dd * (size_t)K * (size_t)G;
    int *eu = malloc(sizeof(int) * cap);
    int *ev = malloc(sizeof(int) * cap);
    if (!eu || !ev) {
        printf("0 0\n");
        return 0;
    }
    size_t m = 0;
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int dupl = 0;
            for (int l2 = 0; l2 < l; l2++) {
                if (best_cfg.P[l2][i] == best_cfg.P[l][i] &&
                    best_cfg.S[l2][i] == best_cfg.S[l][i]) {
                    dupl = 1;
                    break;
                }
            }
            if (dupl) continue;
            int j = best_cfg.P[l][i], s = best_cfg.S[l][i];
            for (int g = 0; g < G; g++) {
                eu[m] = i * G + g;
                ev[m] = (K + j) * G + gmul(g, s);
                m++;
            }
        }
    }
    printf("%d %zu\n", N, m);
    for (size_t e = 0; e < m; e++) {
        printf("%d %d\n", eu[e], ev[e]);
    }
    free(eu);
    free(ev);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions first, then the annealing search in C.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(3.0, min(0.85 * time_limit, time_limit - 6.0))
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
        try:
            if n > best_n and lib.is_valid(n, e, d, D):
                best = (n, e)
                best_n = n
        except Exception:
            pass

    # Exact constructions.
    if D >= 3:
        try:
            pg = _best_pg(d)
        except Exception:
            pg = None
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < deadline:
        try:
            gq = _best_gq(d)
        except Exception:
            gq = None
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Annealing search over bi-Cayley lifts, aiming above the Moore-fraction
    # target and adapting downward when runs fail.
    if d >= 3 and D >= 3 and d <= 16:
        remaining = deadline - time.monotonic()
        if remaining >= 3.0:
            aim = max(best_n + 1, int(0.372 * lib.moore_bound(d, D)))
            try:
                out = lib.run_c(
                    C_SOURCE,
                    [d, D, seed, f"{remaining - 1.5:.2f}", best_n, aim],
                    timeout=time_limit - 3.0,
                )
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
