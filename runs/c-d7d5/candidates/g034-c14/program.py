import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact constructions and small-case baselines.
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


def _cycle(D):
    """Cycle on 2D vertices: bipartite, max degree 2, diameter D (optimal for d = 2)."""
    n = 2 * D
    return n, [(i, (i + 1) % n) for i in range(n)]


# Known record orders used only as search hints (never as outputs).
RECORDS = {(7, 5): 1134}


# ----------------------------------------------------------------------------
# C engine: simulated annealing over bi-Cayley graphs with a fresh move set.
#
# Vertices: A_{i,g} = i*G+g, B_{j,h} = (K+j)*G+h, for i, j < K and g, h in the
# group H = Z_m x| Z_k (element (a,b) coded as a*k+b). Layer l, block i gives
# the matching A_{i,g} -- B_{P[l][i], g*S[l][i]}. Each layer is a perfect
# matching, so every vertex has degree exactly Dd. Left multiplication by H is
# an automorphism, so the diameter is checked from the 2K block representatives.
#
# Cost = unreached (representative, vertex) pairs within DD steps + PEN * duplicate
# edges. Cost 0 means a valid graph. Moves: resample one voltage or swap two
# block targets within one layer. Metropolis acceptance, geometric cooling.
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
#define MAXS 16
#define GMAX 3000
#define PEN 40

typedef struct {
    int K;
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

static int Dd = 3, DD = 3;
static double deadline = 0.0;

static int GM = 1, GK = 1, GG = 1;
static long long pw[64];

static void set_group(int m, int k, int r) {
    GM = m;
    GK = k;
    GG = m * k;
    long long p = 1 % m;
    for (int b = 0; b < k; b++) {
        pw[b] = p;
        p = (p * (long long)r) % m;
    }
}

static int gmul(int x, int y) {
    int a = x / GK, b = x % GK;
    int c = y / GK, d = y % GK;
    long long t = ((long long)a + pw[b] * (long long)c) % GM;
    return (int)t * GK + (b + d) % GK;
}

static int capN = 0;
static int *adj = NULL, *vis = NULL, *qu = NULL;
static int stamp = 0;

static void ensure_cap(int N) {
    if (N <= capN) return;
    free(adj);
    free(vis);
    free(qu);
    adj = malloc(sizeof(int) * (size_t)N * MAXD);
    vis = calloc((size_t)N, sizeof(int));
    qu = malloc(sizeof(int) * (size_t)N);
    if (!adj || !vis || !qu) {
        fprintf(stderr, "out of memory\n");
        exit(1);
    }
    capN = N;
    stamp = 0;
}

static int g_dup = 0;
static long long g_raw = 0;

static long long evaluate(const Cfg *c) {
    int K = c->K, G = GG, N = 2 * K * G;
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = c->P[l][i], s = c->S[l][i];
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                int b = (K + j) * G + gmul(g, s);
                adj[a * MAXD + l] = b;
                adj[b * MAXD + l] = a;
            }
        }
    }
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < Dd; l1++)
            for (int l2 = l1 + 1; l2 < Dd; l2++)
                if (c->P[l1][i] == c->P[l2][i] && c->S[l1][i] == c->S[l2][i])
                    dup++;
    g_dup = dup;

    long long raw = 0;
    for (int blk = 0; blk < 2 * K; blk++) {
        int src = blk * G;
        stamp++;
        int head = 0, tail = 0;
        vis[src] = stamp;
        qu[tail++] = src;
        for (int lv = 0; lv < DD && head < tail; lv++) {
            int end = tail;
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
        raw += (long long)(N - tail);
    }
    g_raw = raw;
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

/* Simulated annealing from *c. Writes the best state seen into *out
   (out must not alias c). Returns the best cost. */
static long long anneal(Cfg *c, long iters, double T0, double T1, Cfg *out) {
    long long cur = evaluate(c);
    long long best = cur;
    *out = *c;
    if (best == 0) return 0;
    for (long t = 0; t < iters; t++) {
        if ((t & 255) == 0 && now_s() > deadline) break;
        double T = T0 * pow(T1 / T0, (double)t / (double)iters);
        int K = c->K;
        int mt = 0, ml = 0, mi = 0, mj = 0, mold = 0;
        if (K >= 2 && rdbl() < 0.3) {
            mt = 1;
            ml = rint_(Dd);
            mi = rint_(K);
            mj = rint_(K - 1);
            if (mj >= mi) mj++;
            int tmp = c->P[ml][mi];
            c->P[ml][mi] = c->P[ml][mj];
            c->P[ml][mj] = tmp;
        } else {
            ml = rint_(Dd);
            mi = rint_(K);
            mold = c->S[ml][mi];
            int ns = rint_(GG);
            if (GG > 1)
                while (ns == mold) ns = rint_(GG);
            c->S[ml][mi] = ns;
        }
        long long nc = evaluate(c);
        if (nc <= cur || rdbl() < exp(-(double)(nc - cur) / T)) {
            cur = nc;
            if (cur < best) {
                best = cur;
                *out = *c;
                if (best == 0) break;
            }
        } else {
            if (mt) {
                int tmp = c->P[ml][mi];
                c->P[ml][mi] = c->P[ml][mj];
                c->P[ml][mj] = tmp;
            } else {
                c->S[ml][mi] = mold;
            }
        }
    }
    return best;
}

static const int KF[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 21,
                         24, 27, 28, 30, 36};

static long long gcdl(long long a, long long b) {
    while (b) {
        long long t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static long long pmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Choose Z_m x| Z_k with m * k = G. Falls back to the direct product r = 1. */
static int sample_group(int G, int *om, int *ok, int *orr) {
    int cand[32], nc = 0;
    int nk = (int)(sizeof(KF) / sizeof(KF[0]));
    for (int q = 0; q < nk; q++)
        if (G % KF[q] == 0 && nc < 32) cand[nc++] = KF[q];
    if (nc == 0) return 0;
    int k = cand[rint_(nc)];
    int m = G / k;
    if (m == 1) {
        *om = 1;
        *ok = k;
        *orr = 0;
        return 1;
    }
    if (k == 1) {
        *om = m;
        *ok = 1;
        *orr = 1;
        return 1;
    }
    for (int t = 0; t < 300; t++) {
        int r = 1 + rint_(m - 1);
        if (gcdl(r, m) != 1) continue;
        if (pmod(r, k, m) != 1 % m) continue;
        *om = m;
        *ok = k;
        *orr = r;
        return 1;
    }
    *om = m;
    *ok = k;
    *orr = 1;
    return 1;
}

int main(int argc, char **argv) {
    Dd = argc > 1 ? atoi(argv[1]) : 3;
    DD = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;
    int min_n = argc > 5 ? atoi(argv[5]) : 0;
    int hint = argc > 6 ? atoi(argv[6]) : 0;

    if (Dd < 1 || Dd > MAXD || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 8; w++) rnd();

    deadline = now_s() + tl;
    int best_n = min_n;
    int have = 0, bM = 1, bK = 1, bR = 1, fails = 0;
    Cfg bestcfg, cur, found, tmp;
    memset(&bestcfg, 0, sizeof bestcfg);
    memset(&cur, 0, sizeof cur);
    memset(&found, 0, sizeof found);
    memset(&tmp, 0, sizeof tmp);

    while (now_s() < deadline) {
        int roll = rint_(100);
        int K = roll < 60 ? 1 : (roll < 92 ? 2 : 3);
        long long base = best_n;
        if (hint > best_n && rint_(100) < 60) base = hint;
        long long lo = base / (2 * K) + 1;
        long long span = lo / 30 + 3 + (long long)(fails / 8) * (lo / 60 + 1);
        if (span > lo / 4 + 5) span = lo / 4 + 5;
        long long G = lo + (long long)rint_((int)span + 1);
        if (G > GMAX / K) continue;

        int M = 1, Kk = 1, R = 1;
        if (!sample_group((int)G, &M, &Kk, &R)) continue;
        set_group(M, Kk, R);
        int N = 2 * K * GG;
        if (N <= best_n) continue;
        ensure_cap(N);

        random_cfg(&cur, K);
        long long bc = anneal(&cur, 30000, 4.0, 0.2, &found);
        if (bc > 0 && bc <= 60 && now_s() < deadline) {
            tmp = found;
            bc = anneal(&tmp, 120000, 1.0, 0.05, &found);
        }
        if (bc == 0 && evaluate(&found) == 0) {
            bestcfg = found;
            bM = M;
            bK = Kk;
            bR = R;
            best_n = N;
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
    int K = bestcfg.K, G = GG;
    int N = 2 * K * G;
    long m = (long)Dd * K * G;
    printf("%d %ld\n", N, m);
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
# Python glue: exact constructions first, then the annealing engine.
# Every returned graph is checked with lib.is_valid; the fallback is K_{d,d}
# (or a cycle for d = 2), which is valid for every case.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(3.0, min(0.85 * time_limit, time_limit - 6.0))

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n, e = _cycle(D)
        if lib.is_valid(n, e, d, D):
            return n, e
        return lib.haar_graph(d, range(d))

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
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Annealing over bi-Cayley graphs, seeded with the best known order.
    if d >= 3 and D >= 3:
        budget = deadline - time.monotonic() - 1.0
        if budget >= 2.0:
            rec = RECORDS.get((d, D), 0)
            hint = int(0.95 * rec) if rec else best_n
            try:
                out = lib.run_c(
                    C_SOURCE,
                    [d, D, seed, f"{budget:.2f}", best_n, hint],
                    timeout=time_limit - 2.0,
                )
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
