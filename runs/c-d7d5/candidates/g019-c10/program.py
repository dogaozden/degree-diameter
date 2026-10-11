import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact baselines (fallbacks and seeds for the search).
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
# C engine: voltage lifts over a FAMILY of finite groups.
#
# Groups are given by full multiplication tables, so the search is not tied to
# cyclic-by-cyclic groups. Families sampled for a given order G:
#   0. metacyclic  Z_m x| Z_k  (power map r, r^k = 1 mod m)
#   1. dihedral    D_{G/2}     (order G, G even)
#   2. abelian     Z_p x Z_{G/p}
# Vertices: A_{i,g} = i*G+g, B_{j,h} = (K+j)*G+h. Dart (l, i) joins
# A_{i,g} to B_{P[l][i], g*S[l][i]}. Since G acts by left multiplication on
# each side, distances from the K+K identity vertices decide the diameter.
# Search: breakout local search (clause weighting) on the weighted count of
# unreached (root, vertex) pairs, plus duplicate-dart penalty. Cost 0 = valid.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXD 16
#define MAXK 3
#define MAXG 2048
#define MAXR (2 * MAXK)
#define MAXN (MAXR * MAXG)
#define PEN 1000
#define POLISH_T 80
#define STUCK 60
#define BREAK_ITERS 30000

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

static int Dd = 7, DD = 5;
static double deadline = 0.0;

/* Group multiplication table, G x G. */
static int G = 1;
static int *MT = NULL;
static long MTcap = 0;

static void table_alloc(int g) {
    if ((long)g * (long)g > MTcap) {
        free(MT);
        MT = malloc(sizeof(int) * (size_t)g * (size_t)g);
        if (!MT) {
            fprintf(stderr, "out of memory\n");
            exit(1);
        }
        MTcap = (long)g * (long)g;
    }
    G = g;
}

static inline int gmul(int x, int y) { return MT[x * G + y]; }

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

/* Z_m x|_r Z_k with element a*k+b and (a,b)(c,d) = (a + r^b c, b + d). */
static void build_meta(int m, int k, int r) {
    table_alloc(m * k);
    int *pw = malloc(sizeof(int) * (size_t)k);
    long long p = 1 % m;
    for (int b = 0; b < k; b++) {
        pw[b] = (int)p;
        p = (p * r) % m;
    }
    for (int x = 0; x < G; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < G; y++) {
            int c = y / k, d = y % k;
            long long A = ((long long)a + (long long)pw[b] * (long long)c) % m;
            MT[x * G + y] = (int)A * k + (b + d) % k;
        }
    }
    free(pw);
}

/* Dihedral group of order 2m: element (a,s) = a*2+s is x -> (-1)^s x + a.
   (a,s)(b,t) = (a + (-1)^s b, s xor t). */
static void build_dihedral(int m) {
    table_alloc(2 * m);
    for (int x = 0; x < G; x++) {
        int a = x >> 1, s = x & 1;
        for (int y = 0; y < G; y++) {
            int b = y >> 1, t = y & 1;
            int A = s ? (a - b) : (a + b);
            A = ((A % m) + m) % m;
            MT[x * G + y] = A * 2 + (s ^ t);
        }
    }
}

/* Direct product Z_p x Z_q, element u*q+v. */
static void build_prod(int p, int q) {
    table_alloc(p * q);
    for (int x = 0; x < G; x++) {
        int u = x / q, v = x % q;
        for (int y = 0; y < G; y++) {
            int w = y / q, z = y % q;
            MT[x * G + y] = ((u + w) % p) * q + (v + z) % q;
        }
    }
}

static void pick_group(int g) {
    int divs[64];
    int nd = 0;
    for (int d = 1; d <= g && nd < 64; d++)
        if (g % d == 0) divs[nd++] = d;
    int fam0 = rint_(3);
    for (int t = 0; t < 3; t++) {
        int f = (fam0 + t) % 3;
        if (f == 1 && (g % 2)) continue;
        if (f == 0) {
            int k = divs[rint_(nd)];
            int m = g / k;
            int r = 1;
            if (k > 1 && m > 2) {
                for (int tr = 0; tr < 300; tr++) {
                    int c = 2 + rint_(m - 2);
                    if (gcdll(c, m) == 1 && powmod(c, k, m) == 1 % m) {
                        r = c;
                        break;
                    }
                }
            }
            build_meta(m, k, r);
            return;
        }
        if (f == 1) {
            build_dihedral(g / 2);
            return;
        }
        int p = divs[rint_(nd)];
        build_prod(p, g / p);
        return;
    }
    build_meta(g, 1, 1);
}

/* Graph storage for the search. */
static int g_adj[MAXN * MAXD];
static int g_cnt[MAXN];
static int g_vis[MAXN];
static int g_q[MAXN];
static long long g_w[MAXR * MAXN];
static int g_stamp = 0;
static long long g_rawcost = 0;
static int g_dup = 0;

static void reset_weights(int K, int N) {
    long long total = (long long)2 * K * N;
    for (long long j = 0; j < total; j++) g_w[j] = 1;
}

/* Returns weighted cost (sum of weights of unreached pairs + PEN * dups).
   Sets g_rawcost to the unweighted cost. If bump != 0, weights of unreached
   pairs grow by one. */
static long long cost_of(const Cfg *c, int bump) {
    int K = c->K;
    int N = 2 * K * G;
    memset(g_cnt, 0, sizeof(int) * (size_t)N);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = c->P[l][i], s = c->S[l][i];
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                int b = (K + j) * G + gmul(g, s);
                g_adj[a * Dd + g_cnt[a]++] = b;
                g_adj[b * Dd + g_cnt[b]++] = a;
            }
        }
    }
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < Dd; l1++)
            for (int l2 = l1 + 1; l2 < Dd; l2++)
                if (c->P[l1][i] == c->P[l2][i] && c->S[l1][i] == c->S[l2][i])
                    dup++;

    long long wsum = 0, raw = 0;
    for (int r = 0; r < 2 * K; r++) {
        int src = r * G;
        g_stamp++;
        int head = 0, tail = 0;
        g_vis[src] = g_stamp;
        g_q[tail++] = src;
        for (int lvl = 0; lvl < DD; lvl++) {
            int end = tail;
            if (head == end) break;
            while (head < end) {
                int u = g_q[head++];
                for (int t = 0; t < Dd; t++) {
                    int v = g_adj[u * Dd + t];
                    if (g_vis[v] != g_stamp) {
                        g_vis[v] = g_stamp;
                        g_q[tail++] = v;
                    }
                }
            }
        }
        long long *w = g_w + (size_t)r * (size_t)N;
        for (int v = 0; v < N; v++) {
            if (g_vis[v] != g_stamp) {
                raw++;
                wsum += w[v];
                if (bump) w[v]++;
            }
        }
    }
    g_dup = dup;
    g_rawcost = raw + (long long)PEN * dup;
    return wsum + (long long)PEN * dup;
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
        for (int i = 0; i < c->K; i++) c->S[l][i] = rint_(G);
    }
}

/* Breakout local search on weighted cost. Returns the best raw cost seen;
   leaves *c at that best state. */
static long long breakout(Cfg *c, long iters) {
    long long wc = cost_of(c, 0);
    long long rc = g_rawcost;
    long long bestraw = rc;
    Cfg bc = *c;
    int stuck = 0;
    for (long t = 0; t < iters && wc != 0; t++) {
        if ((t & 127) == 0 && now_s() > deadline) break;
        int l = rint_(Dd);
        int i = rint_(c->K);
        int kind = (c->K >= 2 && rint_(4) == 0);
        int old_s = 0, i2 = 0;
        if (kind) {
            i2 = rint_(c->K - 1);
            if (i2 >= i) i2++;
            int tmp = c->P[l][i];
            c->P[l][i] = c->P[l][i2];
            c->P[l][i2] = tmp;
        } else {
            old_s = c->S[l][i];
            c->S[l][i] = rint_(G);
        }
        long long wc2 = cost_of(c, 0);
        if (wc2 <= wc) {
            if (wc2 < wc) stuck = 0;
            else stuck++;
            wc = wc2;
            rc = g_rawcost;
            if (rc < bestraw) {
                bestraw = rc;
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
            cost_of(c, 1);
            wc = cost_of(c, 0);
            rc = g_rawcost;
            stuck = 0;
        }
    }
    *c = bc;
    return bestraw;
}

/* Best-improvement coordinate sweeps over every dart value (unit weights). */
static long long polish(Cfg *c) {
    long long cost = cost_of(c, 0);
    int improved = 1;
    while (improved && cost != 0) {
        improved = 0;
        for (int l = 0; l < Dd && cost != 0; l++) {
            for (int i = 0; i < c->K; i++) {
                if (now_s() > deadline) return cost;
                int old = c->S[l][i];
                int bestv = old;
                long long bestc = cost;
                for (int s = 0; s < G; s++) {
                    if (s == old) continue;
                    c->S[l][i] = s;
                    long long c2 = cost_of(c, 0);
                    if (c2 < bestc) {
                        bestc = c2;
                        bestv = s;
                    }
                }
                c->S[l][i] = bestv;
                if (bestv != old) {
                    cost = bestc;
                    improved = 1;
                    if (cost == 0) break;
                }
            }
        }
    }
    return cost;
}

/* Output buffer for the best valid graph found so far. */
static int BEu[MAXD * MAXK * MAXG];
static int BEv[MAXD * MAXK * MAXG];

static int emit(const Cfg *c) {
    int K = c->K, m = 0;
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = c->P[l][i], s = c->S[l][i];
            for (int g = 0; g < G; g++) {
                BEu[m] = i * G + g;
                BEv[m] = (K + j) * G + gmul(g, s);
                m++;
            }
        }
    }
    return m;
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
    for (int w = 0; w < 4; w++) rnd();

    double t0 = now_s();
    deadline = t0 + tl;
    int best_n = min_n;
    int have = 0;
    int out_n = 0, out_m = 0;
    Cfg cur;
    memset(&cur, 0, sizeof(cur));

    while (now_s() < deadline) {
        int r100 = rint_(100);
        int K = (r100 < 55) ? 1 : ((r100 < 90) ? 2 : 3);
        long long gmin = best_n / (2 * K) + 1;
        long long span = gmin / 30 + 3;
        long long g = gmin + (long long)rint_((int)span);
        if (g < 1) g = 1;
        if (g > MAXG) continue;
        long long N = 2LL * K * g;
        if (N <= best_n || N > MAXN) continue;

        pick_group((int)g);
        cur.K = K;
        random_cfg(&cur);
        int Ni = (int)N;
        reset_weights(K, Ni);
        breakout(&cur, BREAK_ITERS);
        cost_of(&cur, 0);
        if (g_rawcost > 0 && g_rawcost <= POLISH_T) {
            reset_weights(K, Ni);
            polish(&cur);
        }
        cost_of(&cur, 0);
        if (g_rawcost == 0) {
            best_n = Ni;
            out_n = Ni;
            out_m = emit(&cur);
            have = 1;
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", out_n, out_m);
    for (int e = 0; e < out_m; e++) printf("%d %d\n", BEu[e], BEv[e]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions first, then the group-family C search.
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

    # Group-family voltage search in C, seeded with the best known order.
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
