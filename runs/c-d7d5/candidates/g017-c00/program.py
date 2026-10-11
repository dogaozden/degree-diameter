import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact baselines (kept as the safe floor).
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
# C engine: simulated annealing over semidirect-product bi-Cayley lifts.
#
# Structure: group H = Z_m x| Z_k (r^k = 1 mod m). Vertices A_{i,g}, B_{j,h},
# i,j < K, g,h in H. Layer l (0..Dd-1) and orbit i: A_{i,g} ~ B_{P[l][i], g*S[l][i]}.
# Each P[l] is a permutation, so every vertex has degree exactly Dd and the
# graph is bipartite by construction. Left translation by H is an automorphism,
# so checking BFS from the 2K orbit representatives suffices.
#
# Cost = (# unreached (representative, vertex) pairs within DD steps)
#        + PEN * (# duplicate parallel darts). Cost 0 means a valid graph.
#
# Search: Metropolis annealing on the raw cost with a geometric temperature
# schedule per attempt. Groups are sampled just above the current best order,
# with K (base orbits per side) drawn from {1,2,3}, so larger base graphs are
# explored than in cyclic-only searches.
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
#define PEN 30
#define MAXN_TOTAL 6000

typedef struct {
    int K, G;
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

static int Dd = 7, DD = 5;
static int GM = 1, GK = 1, GG = 1;
static long long gpow[64];
static double deadline = 0.0;

static void set_group(int m, int k, int r) {
    GM = m;
    GK = k;
    GG = m * k;
    long long p = 1 % m;
    for (int b = 0; b < k; b++) {
        gpow[b] = p;
        p = (p * r) % m;
    }
}

/* (a,b)*(c,d) = (a + r^b c, b + d), element (a,b) coded as a*k + b. */
static int gmul(int x, int y) {
    int a = x / GK, b = x % GK;
    int c = y / GK, d = y % GK;
    long long t = ((long long)a + gpow[b] * (long long)c) % GM;
    return (int)t * GK + (b + d) % GK;
}

static int cap = 0;
static int *adj = NULL, *cnt = NULL, *vis = NULL, *qu = NULL;
static int stamp = 0;

static void ensure(int N) {
    if (N <= cap) return;
    free(adj);
    free(cnt);
    free(vis);
    free(qu);
    cap = N;
    adj = malloc(sizeof(int) * (size_t)N * (size_t)Dd);
    cnt = malloc(sizeof(int) * (size_t)N);
    vis = calloc((size_t)N, sizeof(int));
    qu = malloc(sizeof(int) * (size_t)N);
    if (!adj || !cnt || !vis || !qu) {
        fprintf(stderr, "out of memory\n");
        exit(1);
    }
    stamp = 0;
}

/* Returns raw + PEN*dup. raw = unreached pairs from orbit representatives. */
static long long eval(const Cfg *c, long long *raw_out, long long *dup_out) {
    int K = c->K, G = c->G, N = 2 * K * G;
    ensure(N);
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
    long long dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < Dd; l1++)
            for (int l2 = l1 + 1; l2 < Dd; l2++)
                if (c->P[l1][i] == c->P[l2][i] && c->S[l1][i] == c->S[l2][i])
                    dup++;

    long long raw = 0;
    for (int r = 0; r < 2 * K; r++) {
        int src = r * G;
        stamp++;
        if (stamp == 0x7fffffff) {
            memset(vis, 0, sizeof(int) * (size_t)N);
            stamp = 1;
        }
        int head = 0, tail = 0;
        vis[src] = stamp;
        qu[tail++] = src;
        for (int lvl = 0; lvl < DD && head < tail; lvl++) {
            int end = tail;
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
        raw += (long long)(N - tail);
    }
    *raw_out = raw;
    *dup_out = dup;
    return raw + (long long)PEN * dup;
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

/* Metropolis annealing on the raw cost for up to `slice` seconds.
   Returns 1 and leaves *c at a valid graph, or 0 with *c at the best state. */
static int anneal(Cfg *c, double slice) {
    double t0 = now_s();
    long long raw, dup;
    long long cur = eval(c, &raw, &dup);
    if (raw == 0 && dup == 0) return 1;
    Cfg best = *c;
    long long bestc = cur;
    const double T0 = 2.5, T1 = 0.12;
    for (;;) {
        double now = now_s();
        if (now > deadline || now - t0 > slice) break;
        double frac = (now - t0) / slice;
        double T = T0 * pow(T1 / T0, frac);
        int l = rint_(Dd);
        int i = rint_(c->K);
        int swap = (c->K >= 2 && rint_(3) == 0);
        int i2 = 0, oldS = 0;
        if (swap) {
            i2 = rint_(c->K - 1);
            if (i2 >= i) i2++;
            int t = c->P[l][i];
            c->P[l][i] = c->P[l][i2];
            c->P[l][i2] = t;
        } else {
            oldS = c->S[l][i];
            c->S[l][i] = rint_(GG);
        }
        long long nraw, ndup;
        long long nc = eval(c, &nraw, &ndup);
        long long delta = nc - cur;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cur = nc;
            if (nc < bestc) {
                bestc = nc;
                best = *c;
            }
            if (nraw == 0 && ndup == 0) return 1;
        } else {
            if (swap) {
                int t = c->P[l][i];
                c->P[l][i] = c->P[l][i2];
                c->P[l][i2] = t;
            } else {
                c->S[l][i] = oldS;
            }
        }
    }
    *c = best;
    eval(c, &raw, &dup);
    return (raw == 0 && dup == 0);
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

static void sample_group(long long target, int *oM, int *oK, int *oR) {
    static const int KF[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18,
                             20, 21, 24, 27, 28, 30, 32, 36, 40};
    int nk = (int)(sizeof(KF) / sizeof(KF[0]));
    int k = KF[rint_(nk)];
    long long m = (target + k - 1) / k;
    if (m < 2) m = 2;
    int r = 1;
    if (k > 1 && m >= 3) {
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
    int bM = 1, bK = 1, bR = 1;
    Cfg best_cfg;
    memset(&best_cfg, 0, sizeof(best_cfg));

    while (now_s() < deadline) {
        int r10 = rint_(10);
        int K = (r10 < 2) ? 1 : (r10 < 6 ? 2 : 3);
        long long target = (long long)best_n / (2 * K) + 1;
        long long span = target / 40 + 2;
        long long g = target + (long long)rint_((int)span);

        int M, Kk, R;
        sample_group(g, &M, &Kk, &R);
        set_group(M, Kk, R);
        if (2LL * K * GG > MAXN_TOTAL) continue;
        int N = 2 * K * GG;
        if (N <= best_n) continue;

        double rem = deadline - now_s();
        if (rem < 0.5) break;
        double slice = 4.0;
        if (slice > rem) slice = rem;

        Cfg c;
        memset(&c, 0, sizeof(c));
        c.K = K;
        c.G = GG;
        random_cfg(&c);
        int ok = anneal(&c, slice);
        if (ok && N > best_n) {
            best_n = N;
            best_cfg = c;
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
    int K = best_cfg.K, G = best_cfg.G;
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
# Python glue: exact constructions first, then the C annealer.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(3.0, min(0.9 * time_limit, time_limit - 5.0))

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

    # Simulated annealing over semidirect-product lifts, seeded with the best order so far.
    if d >= 3 and D >= 3:
        c_budget = deadline - time.monotonic() - 1.5
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
