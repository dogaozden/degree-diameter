import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact baselines (safe fallbacks, always checked with lib.is_valid).
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
# C engine: simulated annealing over bi-Cayley graphs on groups Z_m x|_r Z_k.
#
# Vertices: A_{i,g} = i*G+g, B_{j,h} = (K+j)*G+h, dart (l, i) joins
# A_{i,g} to B_{P[l][i], g*S[l][i]}. Left multiplication is an automorphism,
# so distances only need to be checked from the 2K block representatives.
# Cost = unreached (rep, vertex) pairs within DD steps + PEN * duplicate darts.
# Cost 0 means a valid graph. The search targets group orders just above the
# best order found so far, and keeps increasing that bar.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 64
#define MAXK 3
#define GCAP 8000
#define PEN 1000
#define SA_ITERS 120000
#define T0 3.0
#define T1 0.15

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

static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int Dd = 3, DD = 3;
static int GM = 1, GK = 1, GG = 1;
static long long gpow[GCAP];
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

static int gmul(int x, int y) {
    int a = x / GK, b = x % GK;
    int c = y / GK, d = y % GK;
    long long t = ((long long)a + gpow[b] * (long long)c) % GM;
    return (int)t * GK + (b + d) % GK;
}

static int cap = 0;
static int *adj = NULL, *cnt = NULL, *vis = NULL, *qu = NULL;
static int stamp = 0;

static void ensure_cap(int N) {
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

static long long evalcost(const Cfg *c) {
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
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < Dd; l1++)
            for (int l2 = l1 + 1; l2 < Dd; l2++)
                if (c->P[l1][i] == c->P[l2][i] && c->S[l1][i] == c->S[l2][i])
                    dup++;

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
        raw += (long long)(N - tail);
    }
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

/* Simulated annealing; leaves *c at the best state found and returns its cost. */
static long long sa_run(Cfg *c, long iters) {
    long long cur = evalcost(c);
    Cfg best = *c;
    long long bestc = cur;
    double lr = log(T1 / T0);
    double T = T0;
    for (long it = 0; it < iters && bestc > 0; it++) {
        if ((it & 255) == 0) {
            if (now_s() > deadline) break;
            T = T0 * exp(lr * (double)it / (double)iters);
        }
        int kind = (c->K >= 2 && rint_(4) == 0);
        int l = rint_(Dd), i = rint_(c->K), i2 = 0, olds = 0;
        if (kind) {
            i2 = rint_(c->K - 1);
            if (i2 >= i) i2++;
            int t = c->P[l][i];
            c->P[l][i] = c->P[l][i2];
            c->P[l][i2] = t;
        } else {
            olds = c->S[l][i];
            c->S[l][i] = rint_(GG);
        }
        long long nc = evalcost(c);
        long long delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = nc;
            if (nc < bestc) {
                bestc = nc;
                best = *c;
            }
        } else {
            if (kind) {
                int t = c->P[l][i];
                c->P[l][i] = c->P[l][i2];
                c->P[l][i2] = t;
            } else {
                c->S[l][i] = olds;
            }
        }
    }
    *c = best;
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

/* Choose a group of order G: Z_m x|_r Z_k with k | G. Mostly non-cyclic. */
static int pick_group(long long G, int *oM, int *oK, int *oR) {
    int cand[64];
    int nc = 0;
    for (int k = 1; k <= 64 && (long long)k <= G; k++) {
        if (G % k == 0 && G / k >= 2) cand[nc++] = k;
    }
    if (nc == 0) return 0;
    int idx = 0;
    if (nc > 1 && rint_(10) < 6) idx = 1 + rint_(nc - 1);
    int k = cand[idx];
    int m = (int)(G / k);
    int r = 1;
    if (k > 1 && m > 2) {
        for (int t = 0; t < 400; t++) {
            long long c = 2 + (long long)rint_(m - 2);
            if (gcdll(c, m) == 1 && powmod(c, k, m) == 1 % m) {
                r = (int)c;
                break;
            }
        }
    }
    *oM = m;
    *oK = k;
    *oR = r;
    return 1;
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
    for (int w = 0; w < 4; w++) rnd();

    double t0 = now_s();
    deadline = t0 + tl;

    int best_n = min_n;
    int have = 0;
    Cfg bestcfg;
    memset(&bestcfg, 0, sizeof(bestcfg));
    int bM = 1, bK = 1, bR = 1;
    Cfg cur;
    memset(&cur, 0, sizeof(cur));

    while (now_s() < deadline) {
        int r = rint_(100);
        int K = (r < 70) ? 1 : ((r < 92) ? 2 : 3);
        long long lo = (long long)best_n / (2 * K) + 1;
        long long span = lo / 40 + 4;
        long long G = lo + (long long)rint_((int)span);
        if (G > GCAP) continue;
        int M, k, R;
        if (!pick_group(G, &M, &k, &R)) continue;
        set_group(M, k, R);
        int N = 2 * K * GG;
        if (N <= best_n) continue;
        ensure_cap(N);
        cur.K = K;
        cur.G = GG;
        random_cfg(&cur);
        long long c = sa_run(&cur, SA_ITERS);
        if (c == 0) {
            best_n = N;
            bestcfg = cur;
            bM = M;
            bK = k;
            bR = R;
            have = 1;
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    set_group(bM, bK, bR);
    int K = bestcfg.K, G = bestcfg.G;
    int n = 2 * K * G;
    long m = (long)Dd * K * G;
    printf("%d %ld\n", n, m);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = bestcfg.P[l][i], s = bestcfg.S[l][i];
            for (int g = 0; g < G; g++) {
                printf("%d %d\n", i * G + g, (K + j) * G + gmul(g, s));
            }
        }
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions first, then C annealing runs.
# ----------------------------------------------------------------------------

def _search(d, D, seed, budget, min_n):
    """One C search run. Returns (n, edges) if it produced a valid graph above min_n, else None."""
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", min_n],
                        timeout=budget + 4.0)
        n, e = lib.parse_graph_text(out)
        if n > 0 and lib.is_valid(n, e, d, D):
            return n, e
    except Exception:
        pass
    return None


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

    # Annealing runs over bi-Cayley graphs. Run 1 gets most of the budget;
    # run 2 uses a new seed and starts from the improved bar.
    if d >= 3 and D >= 3:
        total = deadline - time.monotonic() - 1.0
        if total >= 4.0:
            r1 = _search(d, D, seed, 0.6 * total, best_n)
            if r1 is not None:
                consider(*r1)
            remaining = deadline - time.monotonic() - 1.0
            if remaining >= 3.0:
                r2 = _search(d, D, seed + 7919, remaining, best_n)
                if r2 is not None:
                    consider(*r2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
