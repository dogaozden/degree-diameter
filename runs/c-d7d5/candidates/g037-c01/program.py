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
# C engine: simulated annealing over bi-Cayley lifts.
#
# Vertices: A_{i,g} = i*G+g, B_{j,h} = (K+j)*G+h, dart (l, i) joins
# A_{i,g} to B_{P[l][i], g*S[l][i]}. Each P[l] is a permutation of K, so the
# graph is Dd-regular and bipartite. Cost = unreached pairs from the 2K
# representative vertices within DD steps + PEN * duplicate darts; cost 0 is
# a valid graph. Moves: resample one voltage, or swap two entries of P[l].
# Metropolis acceptance on a cooling schedule, several restarts per group
# order, and the group order window slides upward after each success.
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
#define MAXGG 2600
#define MAXNV 16000
#define PEN 40
#define ITERS 30000
#define ATTEMPTS 3
#define CHECK_MASK 255

typedef struct {
    int K;
    int P[MAXD][MAXK];
    int S[MAXD][MAXK];
} Cfg;

static int Dd = 7, DD = 5;
static int GM = 1, GK = 1, GG = 1;
static int gpow[64];
static int *MT = NULL;
static long MT_cap = 0;
static double deadline = 0.0;
static uint64_t rs = 88172645463325252ULL;

static int *adjv = NULL, *cnt = NULL, *vis = NULL, *que = NULL;
static int vcap = 0;
static int stamp = 0;
static int g_raw = 0, g_dup = 0;

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

static const int KF[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16,
                         18, 20, 21, 24, 27, 28, 30, 32, 36, 40};
static const int NKF = (int)(sizeof(KF) / sizeof(KF[0]));

static int gmul_raw(int x, int y) {
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
    if (need > MT_cap) {
        free(MT);
        MT = malloc(sizeof(int) * (size_t)need);
        if (!MT) {
            fprintf(stderr, "oom\n");
            exit(1);
        }
        MT_cap = need;
    }
    for (int x = 0; x < GG; x++)
        for (int y = 0; y < GG; y++)
            MT[(long)x * GG + y] = gmul_raw(x, y);
}

static void ensure_v(int N) {
    if (N <= vcap) return;
    free(adjv);
    free(cnt);
    free(vis);
    free(que);
    vcap = N;
    adjv = malloc(sizeof(int) * (size_t)N * MAXD);
    cnt = malloc(sizeof(int) * (size_t)N);
    vis = calloc((size_t)N, sizeof(int));
    que = malloc(sizeof(int) * (size_t)N);
    stamp = 0;
    if (!adjv || !cnt || !vis || !que) {
        fprintf(stderr, "oom\n");
        exit(1);
    }
}

/* Weighted-free cost: unreached rep pairs + PEN * duplicates. */
static long long evaluate(const Cfg *c) {
    int K = c->K;
    int N = 2 * K * GG;
    ensure_v(N);
    for (int v = 0; v < N; v++) cnt[v] = 0;
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = c->P[l][i], s = c->S[l][i];
            for (int g = 0; g < GG; g++) {
                int a = i * GG + g;
                int b = (K + j) * GG + MT[(long)g * GG + s];
                adjv[a * MAXD + cnt[a]++] = b;
                adjv[b * MAXD + cnt[b]++] = a;
            }
        }
    }
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < Dd; l1++)
            for (int l2 = l1 + 1; l2 < Dd; l2++)
                if (c->P[l1][i] == c->P[l2][i] && c->S[l1][i] == c->S[l2][i])
                    dup++;

    if (stamp > 2000000000) {
        memset(vis, 0, sizeof(int) * (size_t)vcap);
        stamp = 0;
    }
    long long raw = 0;
    for (int r = 0; r < 2 * K; r++) {
        stamp++;
        int head = 0, tail = 0;
        int src = r * GG;
        vis[src] = stamp;
        que[tail++] = src;
        for (int lvl = 0; lvl < DD; lvl++) {
            int end = tail;
            if (head == end) break;
            while (head < end) {
                int u = que[head++];
                for (int t = 0; t < Dd; t++) {
                    int v = adjv[u * MAXD + t];
                    if (vis[v] != stamp) {
                        vis[v] = stamp;
                        que[tail++] = v;
                    }
                }
            }
        }
        raw += (long long)(N - tail);
    }
    g_raw = (int)raw;
    g_dup = dup;
    return raw + (long long)PEN * dup;
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

/* Simulated annealing from *c. Returns the best cost; *best holds that state. */
static long long anneal(Cfg *c, Cfg *best) {
    int K = c->K;
    long long cur = evaluate(c);
    long long bestc = cur;
    *best = *c;
    double T0 = 2.0 + 0.05 * (double)cur;
    double T1 = 0.4;
    for (long t = 0; t < ITERS && bestc > 0; t++) {
        if ((t & CHECK_MASK) == 0 && now_s() > deadline) break;
        double T = T0 * pow(T1 / T0, (double)t / (double)ITERS);
        int l = rint_(Dd), i = rint_(K);
        int doswap = (K >= 2 && rint_(4) == 0);
        int old_s = 0, i2 = 0;
        if (doswap) {
            i2 = rint_(K - 1);
            if (i2 >= i) i2++;
            int tmp = c->P[l][i];
            c->P[l][i] = c->P[l][i2];
            c->P[l][i2] = tmp;
        } else {
            old_s = c->S[l][i];
            c->S[l][i] = rint_(GG);
        }
        long long nc = evaluate(c);
        long long dlt = nc - cur;
        if (dlt <= 0 || rdbl() < exp(-(double)dlt / T)) {
            cur = nc;
            if (cur < bestc) {
                bestc = cur;
                *best = *c;
            }
        } else {
            if (doswap) {
                int tmp = c->P[l][i];
                c->P[l][i] = c->P[l][i2];
                c->P[l][i2] = tmp;
            } else {
                c->S[l][i] = old_s;
            }
        }
    }
    return bestc;
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

int main(int argc, char **argv) {
    Dd = argc > 1 ? atoi(argv[1]) : 7;
    DD = argc > 2 ? atoi(argv[2]) : 5;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;
    int min_n = argc > 5 ? atoi(argv[5]) : 0;

    if (Dd < 1 || Dd > MAXD || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 8; w++) rnd();

    double t0 = now_s();
    deadline = t0 + tl;
    int best_n = min_n;
    int have = 0;
    int bK = 1, bM = 1, bk = 1, br = 1;
    Cfg bestcfg;
    memset(&bestcfg, 0, sizeof(bestcfg));

    while (now_s() < deadline) {
        int K = (rint_(10) < 6) ? 1 : ((rint_(10) < 8) ? 2 : 3);
        long long glo = (long long)best_n / (2 * K) + 1;
        long long span = glo / 30 + 4;
        long long target = glo + (long long)rint_((int)span);
        int k = KF[rint_(NKF)];
        long long mm = (target + k - 1) / k;
        if (mm < 2) mm = 2;
        if (mm * k > MAXGG) continue;
        int m = (int)mm;
        int r = 1;
        if (k > 1 && m > 2) {
            for (int t = 0; t < 200; t++) {
                long long c = 2 + (long long)rint_(m - 2);
                if (gcdll(c, m) == 1 && powmod(c, k, m) == 1 % m) {
                    r = (int)c;
                    break;
                }
            }
        }
        set_group(m, k, r);
        int N = 2 * K * GG;
        if (N > MAXNV || N <= best_n) continue;

        int found = 0;
        Cfg cur, bc;
        memset(&cur, 0, sizeof(cur));
        memset(&bc, 0, sizeof(bc));
        for (int a = 0; a < ATTEMPTS && !found && now_s() < deadline; a++) {
            random_cfg(&cur, K);
            long long res = anneal(&cur, &bc);
            if (res == 0) found = 1;
        }
        if (found) {
            best_n = N;
            bestcfg = bc;
            bK = K;
            bM = m;
            bk = k;
            br = r;
            have = 1;
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    set_group(bM, bk, br);
    Cfg *c = &bestcfg;
    c->K = bK;
    if (evaluate(c) != 0) {
        printf("0 0\n");
        return 0;
    }
    int K = c->K;
    int n = 2 * K * GG;
    long m = (long)Dd * K * GG;
    printf("%d %ld\n", n, m);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = c->P[l][i], s = c->S[l][i];
            for (int g = 0; g < GG; g++) {
                printf("%d %d\n", i * GG + g, (K + j) * GG + MT[(long)g * GG + s]);
            }
        }
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: safe exact constructions first, then the C annealer.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(4.0, min(0.85 * time_limit, time_limit - 6.0))

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
            if pg is not None:
                consider(pg[0], pg[1])
                if D == 3 and lib.is_prime_power(d - 1):
                    return best
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

    # Simulated annealing over bi-Cayley lifts in C, seeded with the best known order.
    if d >= 3 and D >= 3:
        c_budget = deadline - time.monotonic() - 1.0
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
