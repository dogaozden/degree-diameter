import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C search engine.
#
# Lift construction: group Z_m x| Z_k2 (order G = m*k2, element a*k2+b,
# (a,b)(c,e) = (a + r^b c, b + e)), base with K A-vertices and K B-vertices.
# Each layer l is a permutation of the K indices; dart t = (l, i) joins
# A_i to B_{perm_l(i)} with voltage s_t. Vertex A_{i,g} = i*G+g is adjacent to
# B_{j,g*s} = (K+j)*G + gm[g*G+s]. Every vertex has degree d.
#
# Left translations are automorphisms, so diameter <= D holds iff a BFS of depth
# D from each of the 2K representatives reaches all vertices. Cost = number of
# unreached (representative, vertex) pairs plus a penalty for duplicate darts.
# Simulated annealing uses two moves: change one voltage, or swap two B-endpoints
# inside one layer (which keeps all degrees equal to d).
# A sweep over group orders keeps raising the target vertex count.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 16
#define MAXK 3
#define MAXG 1500
#define MAXN (2 * MAXK * MAXG)
#define MAXL (MAXD * MAXK)

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndi(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rndf(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double nowsec(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int d, D, K, G, Lh;
static int gm[MAXG * MAXG];
static int gM, gK2, gR;
static int gpw[64];
static int rl[MAXG];

static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static void build_group(int m, int k2, int r) {
    gM = m; gK2 = k2; gR = r;
    G = m * k2;
    for (int b = 0; b < k2; b++) gpw[b] = (int)powmod(r, b, m);
    for (int x = 0; x < G; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < G; y++) {
            int c = y / k2, e = y % k2;
            int na = (a + gpw[b] * c) % m;
            int nb = (b + e) % k2;
            gm[x * G + y] = na * k2 + nb;
        }
    }
}

static int choose_group(int Gt, int *om, int *ok2, int *orr) {
    int cand[16], nc = 0;
    for (int k2 = 1; k2 <= 12; k2++)
        if (Gt % k2 == 0 && Gt / k2 >= 2) cand[nc++] = k2;
    if (nc == 0) return 0;
    for (int tries = 0; tries < 30; tries++) {
        int k2 = cand[rndi(nc)];
        int m = Gt / k2;
        int nr = 0;
        for (int r = 1; r < m; r++)
            if (gcd_i(r, m) == 1 && powmod(r, k2, m) == 1 % m) rl[nr++] = r;
        if (nr == 0) continue;
        *om = m; *ok2 = k2; *orr = rl[rndi(nr)];
        return 1;
    }
    return 0;
}

static int di_[MAXL], dj_[MAXL], sv_[MAXL];
static int adjv[MAXN * MAXD];
static int degc[MAXN];
static int vis[MAXN], dist_[MAXN], qbuf[MAXN];
static int stamp = 0;

static long eval_cost(void) {
    int N = 2 * K * G;
    long dup = 0;
    for (int t = 0; t < Lh; t++)
        for (int u = 0; u < t; u++)
            if (di_[t] == di_[u] && dj_[t] == dj_[u] && sv_[t] == sv_[u]) dup++;
    for (int v = 0; v < N; v++) degc[v] = 0;
    for (int t = 0; t < Lh; t++) {
        int i = di_[t], j = dj_[t], s = sv_[t];
        for (int g = 0; g < G; g++) {
            int a = i * G + g;
            int b = (K + j) * G + gm[g * G + s];
            adjv[a * MAXD + degc[a]++] = b;
            adjv[b * MAXD + degc[b]++] = a;
        }
    }
    long total = 0;
    for (int r = 0; r < 2 * K; r++) {
        int src = (r < K) ? r * G : (K + (r - K)) * G;
        stamp++;
        int head = 0, tail = 0;
        qbuf[tail++] = src;
        vis[src] = stamp;
        dist_[src] = 0;
        while (head < tail) {
            int u = qbuf[head++];
            if (dist_[u] >= D) continue;
            for (int e = 0; e < degc[u]; e++) {
                int w = adjv[u * MAXD + e];
                if (vis[w] != stamp) {
                    vis[w] = stamp;
                    dist_[w] = dist_[u] + 1;
                    qbuf[tail++] = w;
                }
            }
        }
        total += N - tail;
    }
    return dup * N + total;
}

static long sa_run(long steps, double deadline) {
    int perm[MAXK];
    Lh = d * K;
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndi(i + 1);
            int tmp = perm[i]; perm[i] = perm[j]; perm[j] = tmp;
        }
        for (int i = 0; i < K; i++) {
            int t = l * K + i;
            di_[t] = i;
            dj_[t] = perm[i];
            sv_[t] = rndi(G);
        }
    }
    long cost = eval_cost();
    double T0 = 3.0, Tend = 0.15;
    for (long st = 0; st < steps && cost > 0; st++) {
        if ((st & 511) == 0 && nowsec() > deadline) break;
        double T = T0 * pow(Tend / T0, (double)st / (double)steps);
        if (K > 1 && rndi(10) < 4) {
            int l = rndi(d), i1 = rndi(K), i2 = rndi(K - 1);
            if (i2 >= i1) i2++;
            int t1 = l * K + i1, t2 = l * K + i2;
            int tmp = dj_[t1]; dj_[t1] = dj_[t2]; dj_[t2] = tmp;
            long c2 = eval_cost();
            if (c2 <= cost || rndf() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                tmp = dj_[t1]; dj_[t1] = dj_[t2]; dj_[t2] = tmp;
            }
        } else {
            int t = rndi(Lh);
            int old = sv_[t];
            sv_[t] = rndi(G);
            long c2 = eval_cost();
            if (c2 <= cost || rndf() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                sv_[t] = old;
            }
        }
    }
    return cost;
}

static int best_n = 0, bK, bm, bk2, br, bL, bG;
static int bdi[MAXL], bdj[MAXL], bsv[MAXL];

static void record_best(long n) {
    best_n = (int)n;
    bK = K; bm = gM; bk2 = gK2; br = gR; bG = G; bL = Lh;
    memcpy(bdi, di_, sizeof(int) * Lh);
    memcpy(bdj, dj_, sizeof(int) * Lh);
    memcpy(bsv, sv_, sizeof(int) * Lh);
}

static void output_best(void) {
    if (best_n == 0) {
        printf("0 0\n");
        return;
    }
    build_group(bm, bk2, br);
    K = bK;
    Lh = d * K;
    memcpy(di_, bdi, sizeof(int) * Lh);
    memcpy(dj_, bdj, sizeof(int) * Lh);
    memcpy(sv_, bsv, sizeof(int) * Lh);
    long M = (long)Lh * G;
    printf("%d %ld\n", best_n, M);
    for (int t = 0; t < Lh; t++) {
        int i = di_[t], j = dj_[t], s = sv_[t];
        for (int g = 0; g < G; g++) {
            int a = i * G + g;
            int b = (K + j) * G + gm[g * G + s];
            printf("%d %d\n", a, b);
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    long min_n = (argc > 5) ? atol(argv[5]) : 0;
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 10; w++) rnd64();

    double deadline = nowsec() + tl;
    if (d < 3 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }

    static const int kchoice[5] = {1, 1, 2, 2, 3};
    while (nowsec() < deadline) {
        int Kc = kchoice[rndi(5)];
        int Gt = (int)(min_n / (2 * Kc)) + 1 + rndi(3);
        if (Gt > MAXG) break;
        int m, k2, r;
        if (!choose_group(Gt, &m, &k2, &r)) continue;
        build_group(m, k2, r);
        K = Kc;
        int found = 0;
        for (int att = 0; att < 6 && !found && nowsec() < deadline; att++) {
            long c = sa_run(30000, deadline);
            if (c == 0) found = 1;
        }
        if (found) {
            long n = 2L * K * G;
            if (n > best_n) record_best(n);
            if (n > min_n) min_n = n;
        }
    }
    output_best();
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions (glue and safe baselines).
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(g):
        nonlocal best
        n, e = g
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg)
        # Araujo-Pardo & Lopez: degree q+2 with q = d-2 a prime power.
        if d >= 5 and lib.is_prime_power(d - 2):
            try:
                consider(lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

    if D == 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq)

    # Moore bound already met: nothing to search for (e.g. calibration cases).
    if D >= 3 and 3 <= d <= 16 and best[0] < lib.moore_bound(d, D):
        elapsed = time.monotonic() - t0
        cbudget = 0.8 * time_limit - elapsed - 1.0
        if cbudget > 2.0:
            try:
                timeout = max(1.0, time_limit * 0.92 - (time.monotonic() - t0))
                out = lib.run_c(C_SOURCE,
                                [d, D, seed & 0xFFFFFFFF, f"{cbudget:.2f}", best[0]],
                                timeout=timeout)
                n, e = lib.parse_graph_text(out)
                consider((n, e))
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
