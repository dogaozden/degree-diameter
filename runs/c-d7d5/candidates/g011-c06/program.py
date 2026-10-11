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
# C engine.
#
# Mode "cayley": bi-Cayley simulated annealing (the parent's search, unchanged
#   in spirit), with a coordinate polish. Prints a valid graph or "0 0".
#
# Mode "repair" (NEW, a different construction family): general bipartite local
#   search on an explicit graph, read from stdin. The state is any graph with
#   max degree <= d. Moves are edge insertions (which evict an edge from a full
#   endpoint) and degree-preserving double-edge swaps. The cost is the number of
#   vertex pairs at distance > D, computed exactly with bitset ball growth.
#   The search repeatedly appends one new vertex and anneals to cost 0. On
#   success it keeps the bigger graph; after repeated failures it stops.
#   It always prints the best VALID graph it has (the input if nothing grows).
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

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

/* ============================ bi-Cayley search ============================ */

#define MAXD 64
#define MAXK 3
#define PEN 1000
#define POLISH_T 80

typedef struct {
    int K, G;
    int P[MAXD][MAXK];
    int S[MAXD][MAXK];
} Cfg;

static int Dd = 3, DD = 3;
static int GM = 1, GK = 1, GG = 1;
static int gpow[64];
static double deadline = 0.0;
static long ITERS = 40000;
static int cap = 0;
static int *g_adj = NULL, *g_cnt = NULL, *g_vis = NULL, *g_q = NULL;
static int g_stamp = 0;

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

static void ensure_cap(int N) {
    if (N <= cap) return;
    free(g_adj);
    free(g_cnt);
    free(g_vis);
    free(g_q);
    cap = N;
    g_adj = malloc(sizeof(int) * (size_t)N * (size_t)Dd);
    g_cnt = malloc(sizeof(int) * (size_t)N);
    g_vis = calloc((size_t)N, sizeof(int));
    g_q = malloc(sizeof(int) * (size_t)N);
    if (!g_adj || !g_cnt || !g_vis || !g_q) {
        fprintf(stderr, "out of memory\n");
        exit(1);
    }
    g_stamp = 0;
}

static int cost_of(const Cfg *c) {
    int K = c->K, G = c->G, N = 2 * K * G;
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

    long unreached = 0;
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
        unreached += N - tail;
    }
    return (int)unreached + PEN * dup;
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

static int anneal(Cfg *c, long iters, double T0) {
    int cost = cost_of(c);
    int bestc = cost;
    Cfg bc = *c;
    for (long t = 0; t < iters && cost != 0; t++) {
        if ((t & 255) == 0 && now_s() > deadline) break;
        double temp = T0 * (1.0 - (double)t / (double)iters) + 0.02;
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
            c->S[l][i] = rint_(GG);
        }
        int c2 = cost_of(c);
        if (c2 <= cost || rdbl() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            if (cost < bestc) {
                bestc = cost;
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
        }
    }
    *c = bc;
    return bestc;
}

static int polish(Cfg *c) {
    int cost = cost_of(c);
    int improved = 1;
    while (improved && cost != 0) {
        improved = 0;
        for (int l = 0; l < Dd && cost != 0; l++) {
            for (int i = 0; i < c->K; i++) {
                if (now_s() > deadline) return cost;
                int old = c->S[l][i];
                int bestv = old, bestc = cost;
                for (int s = 0; s < GG; s++) {
                    if (s == old) continue;
                    c->S[l][i] = s;
                    int c2 = cost_of(c);
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

static const int KF[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16,
                         18, 20, 21, 24, 27, 28, 30, 32, 36, 40};

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

static int run_cayley(int d_, int D_, unsigned long long seed, double tl, int min_n) {
    Dd = d_;
    DD = D_;
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
    int bM = 1, bK = 1, bR = 1;
    Cfg cur, best_cfg;
    memset(&cur, 0, sizeof(cur));
    memset(&best_cfg, 0, sizeof(best_cfg));

    while (now_s() < deadline) {
        int K = (rint_(100) < 75) ? 1 : 2;
        long long g0 = (long long)best_n / (2 * K) + 1;
        long long span = g0 / 25 + 6;
        long long g = g0 + (long long)rint_((int)span);

        int M, Kk, R;
        sample_group(g, &M, &Kk, &R);
        set_group(M, Kk, R);
        if (GG > 6000) continue;
        int N = 2 * K * GG;
        if (N <= best_n) continue;

        cur.K = K;
        cur.G = GG;
        ensure_cap(N);
        random_cfg(&cur);
        int c = anneal(&cur, ITERS, 1.5);
        if (c > 0 && c <= POLISH_T) c = polish(&cur);
        if (c == 0) {
            best_n = N;
            best_cfg = cur;
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

/* ====================== general bipartite repair search ====================== */

static int RD = 3, RDD = 3;
static int cap_n = 0, Wcap = 0, n_cur = 0, best_n_r = 0;
static int *radj = NULL, *rdeg = NULL, *bestadj = NULL, *bestdeg = NULL;
static unsigned char *rside = NULL;
static uint64_t *bA = NULL, *bB = NULL;

typedef struct {
    int op, x, y;
} Op;
static Op logv[32];
static int nlog = 0;

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void add_e(int x, int y) {
    radj[x * RD + rdeg[x]++] = y;
    radj[y * RD + rdeg[y]++] = x;
}

static void del_half(int x, int y) {
    int *a = radj + x * RD;
    for (int k = 0; k < rdeg[x]; k++) {
        if (a[k] == y) {
            a[k] = a[rdeg[x] - 1];
            rdeg[x]--;
            return;
        }
    }
}

static void del_e(int x, int y) {
    del_half(x, y);
    del_half(y, x);
}

static int has_edge(int x, int y) {
    int *a = radj + x * RD;
    for (int k = 0; k < rdeg[x]; k++)
        if (a[k] == y) return 1;
    return 0;
}

static void L_add(int x, int y) {
    add_e(x, y);
    logv[nlog].op = 1;
    logv[nlog].x = x;
    logv[nlog].y = y;
    nlog++;
}

static void L_del(int x, int y) {
    del_e(x, y);
    logv[nlog].op = 0;
    logv[nlog].x = x;
    logv[nlog].y = y;
    nlog++;
}

static void undo_all(void) {
    while (nlog > 0) {
        nlog--;
        if (logv[nlog].op)
            del_e(logv[nlog].x, logv[nlog].y);
        else
            add_e(logv[nlog].x, logv[nlog].y);
    }
}

/* Exact cost: number of unordered pairs at distance > RDD (bitset ball growth). */
static long eval_cost(void) {
    int n = n_cur, Wn = (n + 63) >> 6, S = Wcap;
    for (int v = 0; v < n; v++) {
        uint64_t *c = bA + (size_t)v * S;
        for (int w = 0; w < Wn; w++) c[w] = 0;
        c[v >> 6] |= 1ULL << (v & 63);
    }
    uint64_t *cur = bA, *nxt = bB;
    for (int t = 0; t < RDD; t++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * S;
            uint64_t *src = cur + (size_t)v * S;
            for (int w = 0; w < Wn; w++) dst[w] = src[w];
            for (int k = 0; k < rdeg[v]; k++) {
                int u = radj[v * RD + k];
                uint64_t *su = cur + (size_t)u * S;
                for (int w = 0; w < Wn; w++) dst[w] |= su[w];
            }
        }
        uint64_t *tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    long bad = 0;
    for (int v = 0; v < n; v++) {
        uint64_t *c = cur + (size_t)v * S;
        long cnt = 0;
        for (int w = 0; w < Wn; w++) cnt += popc64(c[w]);
        bad += n - cnt;
    }
    return bad / 2;
}

/* Random vertex on the given side; prefers vertices with spare degree when asked. */
static int pick_side(int side, int want_def) {
    int n = n_cur;
    for (int t = 0; t < 12; t++) {
        int v = rint_(n);
        if (rside[v] != side) continue;
        if (!want_def || rdeg[v] < RD) return v;
    }
    for (int t = 0; t < 4 * n; t++) {
        int v = rint_(n);
        if (rside[v] == side) return v;
    }
    return -1;
}

/* Insert edge x-y (opposite sides); a full endpoint first drops one random edge. */
static int move_insert(void) {
    int s = rint_(2);
    int x = pick_side(s, rint_(2) == 0);
    int y = pick_side(1 - s, rint_(2) == 0);
    if (x < 0 || y < 0) return 0;
    if (has_edge(x, y)) return 0;
    if (rdeg[x] >= RD) {
        int z = radj[x * RD + rint_(rdeg[x])];
        L_del(x, z);
    }
    if (rdeg[y] >= RD) {
        int z = radj[y * RD + rint_(rdeg[y])];
        L_del(y, z);
    }
    L_add(x, y);
    return 1;
}

/* Degree-preserving double-edge swap: a-b, c-e  ->  a-e, c-b (a, c same side). */
static int move_swap(void) {
    int n = n_cur;
    int a = rint_(n);
    if (rdeg[a] == 0) return 0;
    int b = radj[a * RD + rint_(rdeg[a])];
    int c = rint_(n);
    if (c == a || rside[c] != rside[a] || rdeg[c] == 0) return 0;
    int e = radj[c * RD + rint_(rdeg[c])];
    if (e == b) return 0;
    if (has_edge(a, e) || has_edge(c, b)) return 0;
    L_del(a, b);
    L_del(c, e);
    L_add(a, e);
    L_add(c, b);
    return 1;
}

static long anneal_until(double t_end, double T0) {
    long cost = eval_cost();
    double t_start = now_s();
    double span = t_end - t_start;
    double frac = 0.0;
    long it = 0;
    while (cost > 0) {
        if ((it & 31) == 0) {
            double t = now_s();
            if (t >= t_end) break;
            frac = (span > 0) ? (t - t_start) / span : 1.0;
        }
        it++;
        double temp = T0 * (1.0 - frac) + 0.05;
        nlog = 0;
        int ok = (rint_(10) < 4) ? move_insert() : move_swap();
        if (!ok) {
            nlog = 0;
            continue;
        }
        long c2 = eval_cost();
        if (c2 <= cost || rdbl() < exp(-(double)(c2 - cost) / temp))
            cost = c2;
        else
            undo_all();
        nlog = 0;
    }
    return cost;
}

static void save_best(void) {
    best_n_r = n_cur;
    for (int v = 0; v < n_cur; v++) {
        bestdeg[v] = rdeg[v];
        memcpy(bestadj + (size_t)v * RD, radj + (size_t)v * RD, sizeof(int) * (size_t)RD);
    }
}

static void restore_best(void) {
    n_cur = best_n_r;
    nlog = 0;
    for (int v = 0; v < n_cur; v++) {
        rdeg[v] = bestdeg[v];
        memcpy(radj + (size_t)v * RD, bestadj + (size_t)v * RD, sizeof(int) * (size_t)RD);
    }
}

static int run_repair(int d_, int D_, unsigned long long seed, double tl) {
    RD = d_;
    RDD = D_;
    if (RD < 1 || RD > MAXD || RDD < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 777ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 4; w++) rnd();

    double t_end = now_s() + tl;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 < 1 || m0 < 0) {
        printf("0 0\n");
        return 0;
    }
    int *eu = malloc(sizeof(int) * (size_t)(m0 > 0 ? m0 : 1));
    int *ev = malloc(sizeof(int) * (size_t)(m0 > 0 ? m0 : 1));
    if (!eu || !ev) {
        printf("0 0\n");
        return 0;
    }
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) {
            m0 = i;
            break;
        }
    }

    cap_n = n0 + 1024;
    Wcap = (cap_n + 63) >> 6;
    radj = malloc(sizeof(int) * (size_t)cap_n * (size_t)RD);
    bestadj = malloc(sizeof(int) * (size_t)cap_n * (size_t)RD);
    rdeg = calloc((size_t)cap_n, sizeof(int));
    bestdeg = calloc((size_t)cap_n, sizeof(int));
    rside = calloc((size_t)cap_n, 1);
    bA = calloc((size_t)cap_n * (size_t)Wcap, sizeof(uint64_t));
    bB = calloc((size_t)cap_n * (size_t)Wcap, sizeof(uint64_t));
    int *col = malloc(sizeof(int) * (size_t)n0);
    int *q = malloc(sizeof(int) * (size_t)n0);
    if (!radj || !bestadj || !rdeg || !bestdeg || !rside || !bA || !bB || !col || !q) {
        printf("0 0\n");
        return 0;
    }

    n_cur = n0;
    for (int i = 0; i < m0; i++) {
        int u = eu[i], v = ev[i];
        if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) continue;
        if (rdeg[u] >= RD || rdeg[v] >= RD) continue;
        if (has_edge(u, v)) continue;
        add_e(u, v);
    }
    free(eu);
    free(ev);

    /* 2-colour the input; keep only edges that cross the colouring. */
    for (int i = 0; i < n0; i++) col[i] = -1;
    for (int s = 0; s < n0; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int v = q[h++];
            for (int k = 0; k < rdeg[v]; k++) {
                int u = radj[v * RD + k];
                if (col[u] < 0) {
                    col[u] = 1 - col[v];
                    q[t++] = u;
                }
            }
        }
    }
    for (int v = 0; v < n0; v++) rside[v] = (unsigned char)col[v];
    for (int v = 0; v < n0; v++) {
        for (int k = rdeg[v] - 1; k >= 0; k--) {
            if (k >= rdeg[v]) continue;
            int u = radj[v * RD + k];
            if (rside[u] == rside[v]) del_e(v, u);
        }
    }

    save_best();

    double total = t_end - now_s();
    double slice = total / 8.0;
    if (slice < 1.5) slice = 1.5;
    int fails = 0;
    while (1) {
        double now = now_s();
        if (t_end - now < 0.3) break;
        if (fails >= 6) break;
        restore_best();
        if (n_cur >= cap_n) break;
        n_cur++;
        rside[n_cur - 1] = (unsigned char)rint_(2);
        rdeg[n_cur - 1] = 0;
        double tend = now + slice;
        if (tend > t_end) tend = t_end;
        long c = anneal_until(tend, 3.0);
        if (c == 0) {
            save_best();
            fails = 0;
        } else {
            fails++;
        }
    }

    int n = best_n_r;
    long m = 0;
    for (int v = 0; v < n; v++) m += bestdeg[v];
    m /= 2;
    printf("%d %ld\n", n, m);
    for (int v = 0; v < n; v++) {
        for (int k = 0; k < bestdeg[v]; k++) {
            int u = bestadj[v * RD + k];
            if (u > v) printf("%d %d\n", v, u);
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        printf("0 0\n");
        return 0;
    }
    if (strcmp(argv[1], "cayley") == 0) {
        int d_ = atoi(argv[2]);
        int D_ = atoi(argv[3]);
        unsigned long long seed = strtoull(argv[4], NULL, 10);
        double tl = atof(argv[5]);
        int min_n = argc > 6 ? atoi(argv[6]) : 0;
        return run_cayley(d_, D_, seed, tl, min_n);
    }
    if (strcmp(argv[1], "repair") == 0) {
        int d_ = atoi(argv[2]);
        int D_ = atoi(argv[3]);
        unsigned long long seed = strtoull(argv[4], NULL, 10);
        double tl = atof(argv[5]);
        return run_repair(d_, D_, seed, tl);
    }
    printf("0 0\n");
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue.
#
# Pipeline for D >= 3 (time split inside the total budget):
#   1. exact constructions (PG(2,q), W(q)) and K_{d,d} as safe fallbacks;
#   2. C "cayley" search, ~45% of the remaining time, seeded with the best order;
#   3. C "repair" search, which starts from the best valid graph found so far,
#      grows it one vertex at a time with a general bipartite annealer.
# Every candidate is checked with lib.is_valid before it can replace the best.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(3.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + total

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

    if d >= 3 and D >= 3:
        # Phase 1: bi-Cayley search for a large valid graph.
        remaining = deadline - time.monotonic()
        c1 = 0.45 * remaining
        if c1 >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, ["cayley", d, D, seed, f"{c1:.2f}", best_n],
                                timeout=c1 + 10.0)
                consider(*lib.parse_graph_text(out))
            except Exception:
                pass

        # Phase 2: grow the best valid graph with the general bipartite repair search.
        c2 = deadline - time.monotonic() - 1.0
        if c2 >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, ["repair", d, D, seed, f"{c2:.2f}"],
                                stdin_graph=best, timeout=c2 + 5.0)
                consider(*lib.parse_graph_text(out))
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
