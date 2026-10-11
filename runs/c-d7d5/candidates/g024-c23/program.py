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
# C engine: general bipartite voltage lifts over semidirect groups
# Z_m x|_r Z_k, searched by simulated annealing.
#
# Base graph: K "A" vertices and K "B" vertices. Dart t = i*Dd + l leaves A
# vertex i, enters B vertex tj[t] (each B vertex receives exactly Dd darts),
# and carries a group label ts[t]. Lift: A_{i,g} ~ B_{j,g*s} for each dart.
# Left multiplication is an automorphism and acts regularly on each fibre,
# so it suffices to BFS from one vertex per fibre (2K BFS runs).
# Cost = unreached (source, vertex) pairs within DD steps + PEN * duplicates.
# Cost 0 means a valid graph of order 2*K*G.
# The search keeps a target order, raises it on success, and lowers a
# starting hint slowly while no valid graph is found.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 64
#define MAXK 4
#define MAXT (MAXK * MAXD)
#define GCAP 1500
#define PEN 4

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }

static double urand(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int Dd = 3, DD = 3;
static double gdeadline = 0.0;

/* ---- group Z_m x|_r Z_k, element a*k+b, identity 0 ---- */
static int GM = 1, GK = 1, G = 2;
static int gpow[MAXD];
static int *mt = NULL;      /* mt[x*G+y] = x*y */
static int mt_cap = 0;
static int *ginv = NULL;
static int ginv_cap = 0;

static void set_group(int m, int k, int r) {
    GM = m;
    GK = k;
    G = m * k;
    long long p = 1 % m;
    for (int b = 0; b < k; b++) {
        gpow[b] = (int)p;
        p = (p * r) % m;
    }
    if (G * G > mt_cap) {
        free(mt);
        mt_cap = G * G;
        mt = malloc(sizeof(int) * (size_t)mt_cap);
    }
    if (G > ginv_cap) {
        free(ginv);
        ginv_cap = G;
        ginv = malloc(sizeof(int) * (size_t)ginv_cap);
    }
    if (!mt || !ginv) {
        fprintf(stderr, "out of memory\n");
        exit(1);
    }
    for (int x = 0; x < G; x++) {
        int a = x / k, b = x % k;
        int nb = (k - b) % k;
        int na = (m - (gpow[nb] * a) % m) % m;
        ginv[x] = na * k + nb;
        for (int y = 0; y < G; y++) {
            int c = y / k, d = y % k;
            int t = (a + gpow[b] * c) % m;
            mt[x * G + y] = t * k + (b + d) % k;
        }
    }
}

static int gcdi(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static int powmodi(long long b, int e, int m) {
    long long r = 1 % m, x = b % m;
    while (e > 0) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

/* Random group of order Gt: direct or semidirect Z_m x| Z_k with r^k = 1 mod m. */
static int sample_group(int Gt, int *om, int *ok, int *orr) {
    int divs[MAXD];
    int nd = 0;
    for (int k = 1; k <= MAXD && 2 * k <= Gt; k++)
        if (Gt % k == 0) divs[nd++] = k;
    if (nd == 0) return 0;
    int k = (rint_(2) == 0) ? 1 : divs[rint_(nd)];
    int m = Gt / k;
    int r = 1;
    if (k > 1 && m >= 3) {
        for (int t = 0; t < 300; t++) {
            int c = 2 + rint_(m - 2);
            if (gcdi(c, m) == 1 && powmodi(c, k, m) == 1 % m) {
                r = c;
                break;
            }
        }
    }
    *om = m;
    *ok = k;
    *orr = r;
    return 1;
}

/* ---- configuration ---- */
static int K = 1, T = 1;
static int tj[MAXT], ts[MAXT];
static int bestT_tj[MAXT], bestT_ts[MAXT];
static int bcnt[MAXK];
static int bdart[MAXK][MAXD];
static int *vis = NULL, *que = NULL;
static int vcap = 0;
static int stamp = 0;

static void ensure_vis(int N) {
    if (N <= vcap) return;
    free(vis);
    free(que);
    vcap = N;
    vis = calloc((size_t)N, sizeof(int));
    que = malloc(sizeof(int) * (size_t)N);
    stamp = 0;
    if (!vis || !que) {
        fprintf(stderr, "out of memory\n");
        exit(1);
    }
}

static long long eval_cost(void) {
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < Dd; l1++)
            for (int l2 = l1 + 1; l2 < Dd; l2++) {
                int t1 = i * Dd + l1, t2 = i * Dd + l2;
                if (tj[t1] == tj[t2] && ts[t1] == ts[t2]) dup++;
            }
    for (int j = 0; j < K; j++) bcnt[j] = 0;
    for (int t = 0; t < T; t++) {
        int j = tj[t];
        bdart[j][bcnt[j]++] = t;
    }
    int N = 2 * K * G;
    int KG = K * G;
    long long raw = 0;
    for (int s = 0; s < 2 * K; s++) {
        stamp++;
        int head = 0, tail = 0;
        int src = s * G;
        vis[src] = stamp;
        que[tail++] = src;
        for (int lvl = 0; lvl < DD && head < tail; lvl++) {
            int end = tail;
            while (head < end) {
                int u = que[head++];
                if (u < KG) {
                    int i = u / G, g = u - i * G;
                    const int *row = mt + (size_t)g * G;
                    int base = i * Dd;
                    for (int l = 0; l < Dd; l++) {
                        int t = base + l;
                        int v = (K + tj[t]) * G + row[ts[t]];
                        if (vis[v] != stamp) {
                            vis[v] = stamp;
                            que[tail++] = v;
                        }
                    }
                } else {
                    int rel = u - KG;
                    int j = rel / G, h = rel - j * G;
                    const int *row = mt + (size_t)h * G;
                    for (int c = 0; c < Dd; c++) {
                        int t = bdart[j][c];
                        int i = t / Dd;
                        int v = i * G + row[ginv[ts[t]]];
                        if (vis[v] != stamp) {
                            vis[v] = stamp;
                            que[tail++] = v;
                        }
                    }
                }
            }
        }
        raw += N - tail;
    }
    return raw + (long long)PEN * dup;
}

static void init_cfg(void) {
    for (int t = 0; t < T; t++) {
        tj[t] = t % K;          /* each B vertex gets exactly Dd darts */
        ts[t] = rint_(G);
    }
    for (int it = 0; it < 8 * T; it++) {
        int a = rint_(T), b = rint_(T);
        int tmp = tj[a];
        tj[a] = tj[b];
        tj[b] = tmp;
    }
}

/* Simulated annealing; returns 1 if a cost-0 configuration was reached
   (stored in bestT_*), else 0 with bestT_* holding the lowest cost seen. */
static int anneal(double tlim) {
    double t0 = now_s();
    double end = t0 + tlim;
    if (end > gdeadline) end = gdeadline;
    double span = end - t0;
    if (span <= 0) return 0;
    init_cfg();
    long long cur = eval_cost();
    long long best = cur;
    memcpy(bestT_tj, tj, sizeof(int) * (size_t)T);
    memcpy(bestT_ts, ts, sizeof(int) * (size_t)T);
    const double Ts = 3.0, Te = 0.15;
    double temp = Ts;
    for (long it = 0; best != 0; it++) {
        if ((it & 31) == 0) {
            double nw = now_s();
            if (nw >= end) break;
            temp = Ts * pow(Te / Ts, (nw - t0) / span);
        }
        int kind = rint_(2);
        int a = rint_(T), b = 0, olds = 0;
        if (kind == 0) {
            olds = ts[a];
            ts[a] = rint_(G);
            if (ts[a] == olds) continue;
        } else {
            b = rint_(T);
            if (tj[a] == tj[b]) continue;
            int tmp = tj[a];
            tj[a] = tj[b];
            tj[b] = tmp;
        }
        long long nc = eval_cost();
        long long delta = nc - cur;
        if (delta <= 0 || urand() < exp(-(double)delta / temp)) {
            cur = nc;
            if (cur < best) {
                best = cur;
                memcpy(bestT_tj, tj, sizeof(int) * (size_t)T);
                memcpy(bestT_ts, ts, sizeof(int) * (size_t)T);
            }
        } else {
            if (kind == 0) {
                ts[a] = olds;
            } else {
                int tmp = tj[a];
                tj[a] = tj[b];
                tj[b] = tmp;
            }
        }
    }
    return best == 0;
}

static const int KC[5] = {1, 2, 2, 3, 4};

int main(int argc, char **argv) {
    Dd = argc > 1 ? atoi(argv[1]) : 3;
    DD = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;
    long long hint = argc > 5 ? atoll(argv[5]) : 0;

    if (Dd < 1 || Dd > MAXD || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 4; w++) rnd();

    double t0 = now_s();
    gdeadline = t0 + tl;
    long long min_n = 0;
    int have = 0;
    int sK = 1, sm = 1, sk = 1, sr = 1;
    static int savT_tj[MAXT], savT_ts[MAXT];

    while (1) {
        double rem = gdeadline - now_s();
        if (rem < 0.3) break;
        K = KC[rint_(5)];
        T = K * Dd;
        long long Nt = hint > min_n + 2 ? hint : min_n + 2;
        long long Gmin = (Nt + 2 * K - 1) / (2 * K);
        if (Gmin > GCAP) break;
        long long span = Gmin / 60 + 3;
        int Gt = (int)(Gmin + rint_((int)span));
        if (Gt > GCAP) Gt = GCAP;
        int m, k, r;
        if (!sample_group(Gt, &m, &k, &r)) continue;
        set_group(m, k, r);
        int N = 2 * K * G;
        ensure_vis(N);
        double att = rem / 8.0;
        if (att < 1.0) att = 1.0;
        if (att > 4.0) att = 4.0;
        if (anneal(att)) {
            min_n = N;
            sK = K;
            sm = m;
            sk = k;
            sr = r;
            have = 1;
            memcpy(savT_tj, bestT_tj, sizeof(int) * (size_t)T);
            memcpy(savT_ts, bestT_ts, sizeof(int) * (size_t)T);
        } else if (hint > min_n + 2) {
            long long dec = hint / 100;
            if (dec < 2) dec = 2;
            hint -= dec;
            if (hint < min_n + 2) hint = min_n + 2;
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    K = sK;
    T = K * Dd;
    set_group(sm, sk, sr);
    memcpy(tj, savT_tj, sizeof(int) * (size_t)T);
    memcpy(ts, savT_ts, sizeof(int) * (size_t)T);
    printf("%d %ld\n", 2 * K * G, (long)T * G);
    for (int t = 0; t < T; t++) {
        int i = t / Dd, j = tj[t];
        for (int g = 0; g < G; g++) {
            printf("%d %d\n", i * G + g, (K + j) * G + mt[g * G + ts[t]]);
        }
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions first, then the C search.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(3.0, min(0.85 * time_limit, time_limit - 5.0))

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

    if D == 2:
        return best

    # Exact constructions.
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        if lib.is_prime_power(d - 1):
            return best
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                ar = lib.araujo_lopez_graph(d - 2)
                consider(ar[0], ar[1])
            except Exception:
                pass

    if D == 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Annealed bi-Cayley lift search in C, aimed at orders near the Moore bound
    # fraction and ramped down until valid graphs appear.
    if d >= 3 and D >= 3:
        c_budget = deadline - time.monotonic() - 2.0
        if c_budget >= 2.0:
            hint = max(best_n + 2, int(0.39 * lib.moore_bound(d, D)))
            run_timeout = max(2.0, time_limit - (time.monotonic() - start) - 1.0)
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{c_budget:.2f}", hint],
                                timeout=run_timeout)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
