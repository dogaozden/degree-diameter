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
# C engine: bi-Cayley search over semidirect groups Z_m x|_r Z_k with
# base size K in {1,2,3,4,6} (2K blocks of size G). Group order G is chosen
# so that N = 2*K*G just exceeds the best valid order found so far, and the
# group is sampled among all factorisations G = m*k (exact order, no slack).
# Search: breakout local search on clause weights, coordinate polish for
# near-solutions, and iterated local search from the best near-miss.
#
# Vertices: A_{i,g} = i*G+g, B_{j,h} = (K+j)*G+h, dart (l, i) joins
# A_{i,g} to B_{P[l][i], g*S[l][i]}. Left multiplication by the group is an
# automorphism, so only the 2K block representatives need BFS.
# Raw cost = unreached representative pairs within DD steps + PEN * duplicate
# darts. Raw cost 0 means a valid graph.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXD 64
#define MAXK 6
#define MAXG 8192
#define PEN 1000
#define POLISH_T 120
#define STUCK 60
#define BREAK_ITERS 20000
#define NEAR_PCT 60
#define PERTURB 3
#define STAMP_LIMIT 2000000000

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

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int Dd = 3, DD = 3;
static int GM = 1, GK = 1, GG = 1;
static int gpow[MAXG];
static double deadline = 0.0;

/* Group Z_m x|_r Z_k, element (a,b) coded as a*k+b, order m*k. */
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

static int gmul(int x, int y) {
    int a = x / GK, b = x % GK;
    int c = y / GK, d = y % GK;
    long long t = ((long long)a + (long long)gpow[b] * (long long)c) % GM;
    return (int)t * GK + (b + d) % GK;
}

static int capN = 0;
static int *adj = NULL, *cnt = NULL, *vis = NULL, *qu = NULL;
static long long *wt = NULL;
static int stamp = 0;
static long long raw_cost = 0;

static void ensure_cap(int N) {
    if (N <= capN) return;
    free(adj);
    free(cnt);
    free(vis);
    free(qu);
    free(wt);
    capN = N;
    adj = malloc(sizeof(int) * (size_t)N * (size_t)Dd);
    cnt = malloc(sizeof(int) * (size_t)N);
    vis = calloc((size_t)N, sizeof(int));
    qu = malloc(sizeof(int) * (size_t)N);
    wt = malloc(sizeof(long long) * (size_t)N * 2 * MAXK);
    if (!adj || !cnt || !vis || !qu || !wt) {
        fprintf(stderr, "out of memory\n");
        exit(1);
    }
    stamp = 0;
}

/* Evaluates the configuration in the current group. Returns the weighted
   cost and sets raw_cost. If bump != 0, unreached pairs get weight +1. */
static long long eval(const Cfg *c, int bump) {
    int K = c->K, G = GG, N = 2 * K * G;
    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = c->P[l][i], s = c->S[l][i];
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                int b = (K + j) * G + gmul(g, s);
                if (cnt[a] < Dd && cnt[b] < Dd) {
                    adj[a * Dd + cnt[a]++] = b;
                    adj[b * Dd + cnt[b]++] = a;
                }
            }
        }
    }
    long long dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < Dd; l1++)
            for (int l2 = l1 + 1; l2 < Dd; l2++)
                if (c->P[l1][i] == c->P[l2][i] && c->S[l1][i] == c->S[l2][i])
                    dup++;

    long long wsum = 0, raw = 0;
    for (int r = 0; r < 2 * K; r++) {
        if (stamp >= STAMP_LIMIT) {
            memset(vis, 0, sizeof(int) * (size_t)capN);
            stamp = 0;
        }
        stamp++;
        int head = 0, tail = 0, src = r * G;
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
        long long *w = wt + (size_t)r * (size_t)N;
        for (int v = 0; v < N; v++) {
            if (vis[v] != stamp) {
                raw++;
                wsum += w[v];
                if (bump) w[v]++;
            }
        }
    }
    raw_cost = raw + PEN * dup;
    return wsum + PEN * dup;
}

static void random_cfg(Cfg *c) {
    int K = c->K;
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

/* Breakout local search on weighted cost. Returns the best raw cost seen
   and leaves *c at that best state. */
static long long breakout(Cfg *c, long iters) {
    long long wc = eval(c, 0);
    long long bestraw = raw_cost;
    Cfg bc = *c;
    int stuck = 0;
    for (long t = 0; t < iters && wc != 0; t++) {
        if ((t & 127) == 0 && now_s() > deadline) break;
        int K = c->K;
        int l = rint_(Dd);
        int i = rint_(K);
        int kind = (K >= 2 && rint_(4) == 0);
        int old_s = 0, i2 = 0;
        if (kind) {
            i2 = rint_(K - 1);
            if (i2 >= i) i2++;
            int tmp = c->P[l][i];
            c->P[l][i] = c->P[l][i2];
            c->P[l][i2] = tmp;
        } else {
            old_s = c->S[l][i];
            c->S[l][i] = rint_(GG);
        }
        long long wc2 = eval(c, 0);
        if (wc2 <= wc) {
            if (wc2 < wc) stuck = 0;
            else stuck++;
            wc = wc2;
            if (raw_cost < bestraw) {
                bestraw = raw_cost;
                bc = *c;
            }
        } else {
            if (kind) {
                int tmp = c->P[l][i];
                c->P[l][i] = c->P[l][i2];
                c->P[l][i2] = tmp;
            } else {
                c->S[l][i] = old_s;
            }
            stuck++;
        }
        if (stuck >= STUCK) {
            eval(c, 1);
            wc = eval(c, 0);
            stuck = 0;
        }
    }
    *c = bc;
    return bestraw;
}

/* Best-improvement coordinate sweeps over every dart value, unit cost
   (raw pairs plus duplicate penalty). Leaves *c at the final state. */
static long long polish(Cfg *c) {
    eval(c, 0);
    long long cost = raw_cost;
    int improved = 1;
    while (improved && cost != 0) {
        improved = 0;
        for (int l = 0; l < Dd && cost != 0; l++) {
            for (int i = 0; i < c->K && cost != 0; i++) {
                if (now_s() > deadline) {
                    eval(c, 0);
                    return raw_cost;
                }
                int old = c->S[l][i];
                int bestv = old;
                long long bestc = cost;
                for (int s = 0; s < GG; s++) {
                    if (s == old) continue;
                    c->S[l][i] = s;
                    eval(c, 0);
                    if (raw_cost < bestc) {
                        bestc = raw_cost;
                        bestv = s;
                    }
                }
                c->S[l][i] = bestv;
                if (bestv != old) {
                    cost = bestc;
                    improved = 1;
                }
            }
        }
    }
    eval(c, 0);
    return raw_cost;
}

static int gcdi(int a, int b) {
    while (b) {
        int t = a % b;
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

/* Random semidirect group of exact order G: pick a divisor k of G uniformly,
   m = G / k, and sometimes a nontrivial multiplier r with r^k = 1 mod m. */
static void sample_group(int G, int *oM, int *oK, int *oR) {
    int divs[256];
    int nd = 0;
    for (int d = 1; d <= G && nd < 256; d++)
        if (G % d == 0) divs[nd++] = d;
    int k = divs[rint_(nd)];
    int m = G / k;
    int r = 1;
    if (k > 1 && m > 2 && rint_(2) == 0) {
        for (int t = 0; t < 300; t++) {
            int c = 2 + rint_(m - 2);
            if (gcdi(c, m) == 1 && powmod(c, k, m) == 1 % m) {
                r = c;
                break;
            }
        }
    }
    *oM = m;
    *oK = k;
    *oR = r;
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
    Cfg best_cfg;
    memset(&best_cfg, 0, sizeof(best_cfg));
    int bm = 1, bk = 1, br = 1;

    int have_near = 0;
    Cfg near;
    memset(&near, 0, sizeof(near));
    int nM = 1, nk = 1, nR = 1;
    long long nraw = 0;

    static const int KS[7] = {1, 2, 2, 3, 3, 4, 6};

    while (now_s() < deadline) {
        Cfg cur;
        memset(&cur, 0, sizeof(cur));
        int K, M, Kk, R;
        if (have_near && rint_(100) < NEAR_PCT) {
            K = near.K;
            M = nM;
            Kk = nk;
            R = nR;
            set_group(M, Kk, R);
            cur = near;
            for (int t = 0; t < PERTURB; t++) {
                int l = rint_(Dd);
                int i = rint_(K);
                cur.S[l][i] = rint_(GG);
            }
        } else {
            K = KS[rint_(7)];
            long long gmin = (long long)best_n / (2 * K) + 1;
            long long span = gmin / 40 + 3;
            long long G = gmin + (long long)rint_((int)span);
            if (G >= MAXG) continue;
            sample_group((int)G, &M, &Kk, &R);
            set_group(M, Kk, R);
            cur.K = K;
            random_cfg(&cur);
        }

        int N = 2 * K * GG;
        if (N <= best_n) {
            have_near = 0;
            continue;
        }
        ensure_cap(N);
        for (long long j = 0; j < (long long)2 * K * N; j++) wt[j] = 1;

        breakout(&cur, BREAK_ITERS);
        eval(&cur, 0);
        if (raw_cost > 0) {
            long long thr = POLISH_T;
            if ((long long)N / 4 > thr) thr = (long long)N / 4;
            if (raw_cost <= thr) polish(&cur);
        }
        eval(&cur, 0);

        if (raw_cost == 0) {
            best_n = N;
            best_cfg = cur;
            bm = M;
            bk = Kk;
            br = R;
            have = 1;
            have_near = 0;
        } else if (!have_near || raw_cost <= nraw) {
            near = cur;
            nM = M;
            nk = Kk;
            nR = R;
            nraw = raw_cost;
            have_near = 1;
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    set_group(bm, bk, br);
    int K = best_cfg.K, G = GG;
    int n = 2 * K * G;
    printf("%d %d\n", n, Dd * K * G);
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
# Python glue: exact constructions first, then the C search.
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

    # Bi-Cayley search with base sizes up to 6 and exact-order semidirect
    # groups, seeded with the best order found so far as a lower bound.
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
