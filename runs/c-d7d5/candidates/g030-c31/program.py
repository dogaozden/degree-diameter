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
# C engine: bi-Cayley graphs over semidirect products Z_m x| Z_k, searched by
# simulated annealing on the number of unreached (representative, vertex)
# pairs, with a duplicate-dart penalty. Restarts draw a fresh group order just
# above the best valid order found so far; near-misses are reheated sometimes.
#
# Vertices: A_{i,g} = i*G+g, B_{j,h} = (K+j)*G+h. Dart (l, i) joins
# A_{i,g} to B_{P[l][i], g*S[l][i]}. Each P[l] is a permutation, so the graph is
# Dd-regular and bipartite. The left action of G is an automorphism group that
# is regular on each side, so BFS from the 2K vertices A_{i,e}, B_{j,e} covers
# all pairs.
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
#define PEN 1000
#define MAXG 6000
#define ITERS 150000
#define T0 2.0
#define T1 0.08
#define BIG 1000000000000LL

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

static double urand(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int Dd = 3, DD = 3;
static int GM = 1, GK = 1, GG = 1, G = 1;
static int gpow[64];
static double deadline = 0.0;

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
static int *adj = NULL, *ncnt = NULL, *vis = NULL, *que = NULL;
static int stamp = 0;

static void ensure_cap(int N) {
    if (N <= capN) return;
    free(adj);
    free(ncnt);
    free(vis);
    free(que);
    capN = N;
    adj = malloc(sizeof(int) * (size_t)N * (size_t)Dd);
    ncnt = malloc(sizeof(int) * (size_t)N);
    vis = calloc((size_t)N, sizeof(int));
    que = malloc(sizeof(int) * (size_t)N);
    if (!adj || !ncnt || !vis || !que) {
        fprintf(stderr, "out of memory\n");
        exit(1);
    }
    stamp = 0;
}

/* Penalised cost: unreached (rep, vertex) pairs within DD steps + PEN * duplicate darts.
   Zero iff the graph is simple and has diameter <= DD. */
static long long evalcfg(const Cfg *c) {
    int K = c->K, N = 2 * K * G;
    memset(ncnt, 0, sizeof(int) * (size_t)N);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = c->P[l][i], s = c->S[l][i];
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                int b = (K + j) * G + gmul(g, s);
                if (ncnt[a] >= Dd || ncnt[b] >= Dd) return BIG;
                adj[a * Dd + ncnt[a]++] = b;
                adj[b * Dd + ncnt[b]++] = a;
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
        memset(vis, 0, sizeof(int) * (size_t)N);
        stamp = 0;
    }
    long long raw = 0;
    for (int r = 0; r < 2 * K; r++) {
        stamp++;
        int head = 0, tail = 0;
        int src = r * G;
        vis[src] = stamp;
        que[tail++] = src;
        for (int lv = 0; lv < DD; lv++) {
            int end = tail;
            if (head == end) break;
            while (head < end) {
                int u = que[head++];
                for (int t = 0; t < Dd; t++) {
                    int v = adj[u * Dd + t];
                    if (vis[v] != stamp) {
                        vis[v] = stamp;
                        que[tail++] = v;
                    }
                }
            }
        }
        raw += N - tail;
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

static void perturb(Cfg *c, int times) {
    for (int t = 0; t < times; t++) {
        int l = rint_(Dd);
        int i = rint_(c->K);
        c->S[l][i] = rint_(GG);
    }
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

static const int KF[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 21,
                         24, 28, 30, 32, 36, 40};

static void sample_group(long long target, int *oM, int *oK, int *oR) {
    int nk = (int)(sizeof(KF) / sizeof(KF[0]));
    int k = KF[rint_(nk)];
    long long m = (target + k - 1) / k;
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
    Cfg best, bl, cur, near;
    memset(&best, 0, sizeof(best));
    memset(&bl, 0, sizeof(bl));
    memset(&cur, 0, sizeof(cur));
    memset(&near, 0, sizeof(near));
    int bM = 1, bK = 1, bR = 1;
    int have_near = 0;
    long long near_cost = 0;
    int nM = 1, nK = 1, nR = 1;

    while (now_s() < deadline) {
        int gM, gK, gR;
        int from_near = have_near && (urand() < 0.3);
        if (from_near) {
            gM = nM;
            gK = nK;
            gR = nR;
            set_group(gM, gK, gR);
            G = GG;
            cur = near;
            perturb(&cur, 2);
        } else {
            int Kc = 1;
            double u = urand();
            if (u >= 0.6) Kc = (u < 0.9) ? 2 : 3;
            long long base = (long long)best_n / (2 * Kc) + 1;
            long long span = base / 30 + 3;
            long long target = base + (long long)rint_((int)span);
            sample_group(target, &gM, &gK, &gR);
            set_group(gM, gK, gR);
            G = GG;
            if (GG > MAXG) continue;
            cur.K = Kc;
            random_cfg(&cur);
        }

        int N = 2 * cur.K * G;
        if (N <= best_n) {
            have_near = 0;
            continue;
        }
        ensure_cap(N);

        long long cc = evalcfg(&cur);
        bl = cur;
        long long bc = cc;
        for (long it = 0; it < ITERS && cc != 0; it++) {
            if ((it & 255) == 0 && now_s() > deadline) break;
            double T = T0 * pow(T1 / T0, (double)it / (double)ITERS);
            int l = rint_(Dd);
            int i = rint_(cur.K);
            int swapk = (cur.K >= 2 && rint_(4) == 0);
            int i2 = 0, old = 0;
            if (swapk) {
                i2 = rint_(cur.K - 1);
                if (i2 >= i) i2++;
                int t = cur.P[l][i];
                cur.P[l][i] = cur.P[l][i2];
                cur.P[l][i2] = t;
            } else {
                old = cur.S[l][i];
                cur.S[l][i] = rint_(GG);
            }
            long long cc2 = evalcfg(&cur);
            long long dlt = cc2 - cc;
            if (dlt <= 0 || urand() < exp(-(double)dlt / T)) {
                cc = cc2;
                if (cc < bc) {
                    bc = cc;
                    bl = cur;
                }
            } else {
                if (swapk) {
                    int t = cur.P[l][i];
                    cur.P[l][i] = cur.P[l][i2];
                    cur.P[l][i2] = t;
                } else {
                    cur.S[l][i] = old;
                }
            }
        }

        if (bc == 0) {
            best = bl;
            bM = gM;
            bK = gK;
            bR = gR;
            best_n = N;
            have = 1;
            have_near = 0;
        } else if (!have_near || bc < near_cost) {
            near = bl;
            near_cost = bc;
            nM = gM;
            nK = gK;
            nR = gR;
            have_near = 1;
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    set_group(bM, bK, bR);
    G = GG;
    int K = best.K;
    int N = 2 * K * G;
    long m = (long)Dd * K * G;
    printf("%d %ld\n", N, m);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = best.P[l][i], s = best.S[l][i];
            for (int g = 0; g < G; g++) {
                printf("%d %d\n", i * G + g, (K + j) * G + gmul(g, s));
            }
        }
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions first, then one annealing run in C.
# ----------------------------------------------------------------------------

def _search(d, D, seed, budget, min_n):
    """One C search run. Returns (n, edges) if it produced a valid graph, else None."""
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", min_n],
                        timeout=budget + 3.0)
        n, e = lib.parse_graph_text(out)
        if n > 0 and lib.is_valid(n, e, d, D):
            return n, e
    except Exception:
        pass
    return None


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

    # One annealing run over bi-Cayley graphs; it raises its own lower bound
    # each time it finds a valid graph, starting from the best baseline.
    if d >= 3 and D >= 3:
        remaining = deadline - time.monotonic() - 1.0
        if remaining >= 3.0:
            res = _search(d, D, seed, remaining, best_n)
            if res is not None:
                consider(*res)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
