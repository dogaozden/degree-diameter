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
# Part 1 (bi-Cayley breakout search, from the parent): searches for a bi-Cayley
# graph on Z_m x| Z_k with K base vertices per side. It runs for the first
# PHASE1_FRAC of the budget.
#
# Part 2 (NEW: vertex-pair insertion + bitset annealing repair): starting from
# the best valid graph (the stdin graph or the phase-1 result), repeatedly
# insert two new vertices a (side 0) and b (side 1). Remove d-1 edges x_i-y_i
# forming a matching, then join x_i-b, a-y_i and a-b. Every degree stays at
# most d, the graph stays bipartite, and the order grows by 2. The diameter
# defect is then removed by degree-preserving double-edge swaps under
# simulated annealing. The cost is the number of unordered pairs at distance
# more than D, computed with 64-bit bitset ball expansion. When the cost hits
# 0 the graph is saved and grown again. After STAG_EPOCHS epochs without
# improvement it restarts from the saved best graph.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define MAXD 64
#define MAXK 3
#define PEN 1000
#define POLISH_T 80
#define STUCK 50
#define BREAK_ITERS 25000
#define NEAR_PCT 50
#define PERTURB 3
#define PHASE1_FRAC 0.50
#define END_FRAC 0.93
#define EPOCH 1000
#define STAG_EPOCHS 10

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

/* ---------------- bi-Cayley scoring (parent engine) ---------------- */

static int cap = 0;
static int *g_adj = NULL, *g_cnt = NULL, *g_vis = NULL, *g_q = NULL;
static long long *g_w = NULL;
static int g_stamp = 0;
static long long g_rawcost = 0;
static int g_dup = 0;

static void ensure_cap(int N) {
    if (N <= cap) return;
    free(g_adj);
    free(g_cnt);
    free(g_vis);
    free(g_q);
    free(g_w);
    cap = N;
    g_adj = malloc(sizeof(int) * (size_t)N * (size_t)Dd);
    g_cnt = malloc(sizeof(int) * (size_t)N);
    g_vis = calloc((size_t)N, sizeof(int));
    g_q = malloc(sizeof(int) * (size_t)N);
    g_w = malloc(sizeof(long long) * (size_t)4 * (size_t)N);
    if (!g_adj || !g_cnt || !g_vis || !g_q || !g_w) {
        fprintf(stderr, "out of memory\n");
        exit(1);
    }
    g_stamp = 0;
}

static void reset_weights(int K, int N) {
    long long total = (long long)2 * K * N;
    for (long long j = 0; j < total; j++) g_w[j] = 1;
}

static long long cost_of(const Cfg *c, int bump) {
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
        for (int i = 0; i < c->K; i++) c->S[l][i] = rint_(GG);
    }
}

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
            c->S[l][i] = rint_(GG);
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
                for (int s = 0; s < GG; s++) {
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

/* Phase 1: bi-Cayley breakout search. Returns 1 and the best config if found. */
static int bicayley_phase(double until, int min_n, Cfg *out, int *oM, int *oK, int *oR) {
    deadline = until;
    int best_n = min_n;
    int have = 0;
    int bM = 1, bK = 1, bR = 1;
    Cfg cur, best_cfg, near;
    memset(&cur, 0, sizeof(cur));
    memset(&best_cfg, 0, sizeof(best_cfg));
    memset(&near, 0, sizeof(near));
    int have_near = 0;
    int nM = 1, nK = 1, nR = 1;
    long long nraw = 0;

    while (now_s() < deadline) {
        int K, M, Kk, R;
        int from_near = have_near && (rint_(100) < NEAR_PCT);
        if (from_near) {
            K = near.K;
            M = nM;
            Kk = nK;
            R = nR;
            set_group(M, Kk, R);
            cur = near;
            for (int t = 0; t < PERTURB; t++) {
                int l = rint_(Dd);
                int i = rint_(K);
                cur.S[l][i] = rint_(GG);
            }
        } else {
            K = (rint_(100) < 75) ? 1 : 2;
            long long g0 = (long long)best_n / (2 * K) + 1;
            long long span = g0 / 25 + 6;
            long long g = g0 + (long long)rint_((int)span);
            sample_group(g, &M, &Kk, &R);
            set_group(M, Kk, R);
            if (GG > 6000) continue;
            cur.K = K;
            cur.G = GG;
            random_cfg(&cur);
        }

        int N = 2 * K * GG;
        if (N <= best_n) {
            have_near = 0;
            continue;
        }
        ensure_cap(N);
        reset_weights(K, N);
        breakout(&cur, BREAK_ITERS);
        cost_of(&cur, 0);
        long long thr = (long long)POLISH_T;
        if ((long long)N / 4 > thr) thr = (long long)N / 4;
        if (g_rawcost > 0 && g_rawcost <= thr) {
            reset_weights(K, N);
            polish(&cur);
        }
        cost_of(&cur, 0);
        if (g_rawcost == 0) {
            best_n = N;
            best_cfg = cur;
            bM = M;
            bK = Kk;
            bR = R;
            have = 1;
            have_near = 0;
        } else if (!have_near || g_rawcost <= nraw) {
            near = cur;
            nM = M;
            nK = Kk;
            nR = R;
            nraw = g_rawcost;
            have_near = 1;
        }
    }
    if (!have) return 0;
    *out = best_cfg;
    *oM = bM;
    *oK = bK;
    *oR = bR;
    return 1;
}

/* Expand a bi-Cayley config into an edge list (caller frees). Group must match. */
static void cfg_edges(const Cfg *c, int M, int K, int R,
                      int *n_out, int *m_out, int **eu_out, int **ev_out) {
    set_group(M, K, R);
    int KB = c->K, G = c->G;
    int n = 2 * KB * G, m = Dd * KB * G;
    int *eu = malloc(sizeof(int) * (size_t)m);
    int *ev = malloc(sizeof(int) * (size_t)m);
    int idx = 0;
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < KB; i++) {
            int j = c->P[l][i], s = c->S[l][i];
            for (int g = 0; g < G; g++) {
                eu[idx] = i * G + g;
                ev[idx] = (KB + j) * G + gmul(g, s);
                idx++;
            }
        }
    }
    *n_out = n;
    *m_out = m;
    *eu_out = eu;
    *ev_out = ev;
}

/* ---------------- Phase 2: working graph with bitset scoring ---------------- */

static int wN = 0, wM = 0;
static int *wEU = NULL, *wEV = NULL, *wCol = NULL, *wDeg = NULL, *wAdj = NULL;
static uint64_t *wRA = NULL, *wRB = NULL;
static int capN = 0, capM = 0;
static size_t capR = 0;

static int BestN = 0, BestM = 0;
static int *BestEU = NULL, *BestEV = NULL, *BestCol = NULL;

static void *xr(void *p, size_t bytes) {
    void *q = realloc(p, bytes);
    if (!q) {
        fprintf(stderr, "out of memory\n");
        exit(1);
    }
    return q;
}

static void reserve(int n, int m) {
    if (n > capN) {
        int nc = 2 * n + 64;
        wCol = xr(wCol, sizeof(int) * (size_t)nc);
        wDeg = xr(wDeg, sizeof(int) * (size_t)nc);
        wAdj = xr(wAdj, sizeof(int) * (size_t)nc * (size_t)Dd);
        BestCol = xr(BestCol, sizeof(int) * (size_t)nc);
        capN = nc;
    }
    if (m > capM) {
        int mc = 2 * m + 64;
        wEU = xr(wEU, sizeof(int) * (size_t)mc);
        wEV = xr(wEV, sizeof(int) * (size_t)mc);
        BestEU = xr(BestEU, sizeof(int) * (size_t)mc);
        BestEV = xr(BestEV, sizeof(int) * (size_t)mc);
        capM = mc;
    }
    size_t need = (size_t)n * (size_t)((n + 63) / 64);
    if (need > capR) {
        size_t nr = 2 * need + 64;
        wRA = xr(wRA, sizeof(uint64_t) * nr);
        wRB = xr(wRB, sizeof(uint64_t) * nr);
        capR = nr;
    }
}

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void build_adj(void) {
    for (int v = 0; v < wN; v++) wDeg[v] = 0;
    for (int e = 0; e < wM; e++) {
        int u = wEU[e], v = wEV[e];
        wAdj[u * Dd + wDeg[u]++] = v;
        wAdj[v * Dd + wDeg[v]++] = u;
    }
}

static int has_nb(int x, int y) {
    for (int k = 0; k < wDeg[x]; k++)
        if (wAdj[x * Dd + k] == y) return 1;
    return 0;
}

/* Number of unordered pairs at distance > DD. Zero means valid (given degree
   bound, bipartiteness and no duplicates, which are enforced elsewhere). */
static long long eval_bad(void) {
    build_adj();
    int W = (wN + 63) / 64;
    uint64_t *cur = wRA, *nxt = wRB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)wN * (size_t)W);
    for (int v = 0; v < wN; v++)
        cur[(size_t)v * W + (size_t)(v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < DD; r++) {
        for (int v = 0; v < wN; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            const uint64_t *c = cur + (size_t)v * W;
            memcpy(o, c, sizeof(uint64_t) * (size_t)W);
            for (int k = 0; k < wDeg[v]; k++) {
                const uint64_t *cu = cur + (size_t)wAdj[v * Dd + k] * W;
                for (int w = 0; w < W; w++) o[w] |= cu[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long long tot = 0;
    for (int v = 0; v < wN; v++) {
        int cnt = 0;
        const uint64_t *c = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) cnt += pc64(c[w]);
        tot += wN - cnt;
    }
    return tot / 2;
}

/* Load an arbitrary graph as the working graph. Returns its bad-pair count,
   or -1 if it is malformed (range, degree > Dd, duplicate edge, odd cycle). */
static long long load_from(int n, int m, const int *eu, const int *ev) {
    if (n < 1 || m < 0) return -1;
    for (int e = 0; e < m; e++) {
        if (eu[e] < 0 || eu[e] >= n || ev[e] < 0 || ev[e] >= n || eu[e] == ev[e]) return -1;
    }
    reserve(n, m);
    wN = n;
    wM = m;
    for (int v = 0; v < n; v++) wDeg[v] = 0;
    for (int e = 0; e < m; e++) {
        wDeg[eu[e]]++;
        wDeg[ev[e]]++;
    }
    for (int v = 0; v < n; v++)
        if (wDeg[v] > Dd) return -1;
    for (int e = 0; e < m; e++) {
        wEU[e] = eu[e];
        wEV[e] = ev[e];
    }
    build_adj();
    for (int v = 0; v < n; v++)
        for (int a = 0; a < wDeg[v]; a++)
            for (int b = 0; b < a; b++)
                if (wAdj[v * Dd + a] == wAdj[v * Dd + b]) return -1;

    int *q = malloc(sizeof(int) * (size_t)n);
    for (int v = 0; v < n; v++) wCol[v] = -1;
    for (int s = 0; s < n; s++) {
        if (wCol[s] != -1) continue;
        wCol[s] = 0;
        int head = 0, tail = 0;
        q[tail++] = s;
        while (head < tail) {
            int u = q[head++];
            for (int k = 0; k < wDeg[u]; k++) {
                int v = wAdj[u * Dd + k];
                if (wCol[v] == -1) {
                    wCol[v] = 1 - wCol[u];
                    q[tail++] = v;
                } else if (wCol[v] == wCol[u]) {
                    free(q);
                    return -1;
                }
            }
        }
    }
    free(q);
    for (int e = 0; e < m; e++) {
        if (wCol[wEU[e]] == 1) {
            int t = wEU[e];
            wEU[e] = wEV[e];
            wEV[e] = t;
        }
    }
    return eval_bad();
}

static void save_best(void) {
    BestN = wN;
    BestM = wM;
    memcpy(BestEU, wEU, sizeof(int) * (size_t)wM);
    memcpy(BestEV, wEV, sizeof(int) * (size_t)wM);
    memcpy(BestCol, wCol, sizeof(int) * (size_t)wN);
}

static long long restore_best(void) {
    wN = BestN;
    wM = BestM;
    memcpy(wEU, BestEU, sizeof(int) * (size_t)wM);
    memcpy(wEV, BestEV, sizeof(int) * (size_t)wM);
    memcpy(wCol, BestCol, sizeof(int) * (size_t)wN);
    return eval_bad();
}

/* Insert a pair (a on side 0, b on side 1). Remove d-1 edges x_i-y_i forming a
   matching, then add x_i-b, a-y_i and a-b. Degrees stay <= d, and a and b
   reach exactly d. Returns 0 if no matching could be found. */
static int augment(void) {
    int need = Dd - 1;
    if (need < 1 || wM < need) return 0;
    int *used = calloc((size_t)wN, sizeof(int));
    int *ch = malloc(sizeof(int) * (size_t)need);
    int cnt = 0;
    long tries = 0;
    while (cnt < need && tries < 200000) {
        tries++;
        int e = rint_(wM);
        int x = wEU[e], y = wEV[e];
        if (used[x] || used[y]) continue;
        used[x] = used[y] = 1;
        ch[cnt++] = e;
    }
    if (cnt < need) {
        free(used);
        free(ch);
        return 0;
    }
    int a = wN, b = wN + 1;
    reserve(wN + 2, wM + Dd);
    for (int i = 0; i < need; i++) {
        int e = ch[i];
        int y = wEV[e];
        wEV[e] = b;                 /* x - b, x is side 0, b is side 1 */
        wEU[wM] = a;                /* a - y */
        wEV[wM] = y;
        wM++;
    }
    wEU[wM] = a;                    /* a - b */
    wEV[wM] = b;
    wM++;
    wCol[a] = 0;
    wCol[b] = 1;
    wN += 2;
    free(used);
    free(ch);
    return 1;
}

/* Phase 2: grow from the best valid graph with annealing repair. */
static void phase2(double until) {
    if (BestN == 0 || wM < 2) return;
    long long cost = restore_best();
    if (cost != 0) return;
    int stag = 0;
    long long epbest = cost;
    double lo = log(0.3), hi = log(3.0);
    while (now_s() < until) {
        if (cost == 0) {
            if (wN > BestN) save_best();
            if (!augment()) break;
            cost = eval_bad();
            epbest = cost;
            stag = 0;
            continue;
        }
        double T = exp(lo + rnd01() * (hi - lo));
        for (int it = 0; it < EPOCH && cost != 0; it++) {
            if (now_s() > until) break;
            build_adj();
            int i = rint_(wM), j = rint_(wM);
            if (i == j) continue;
            int x1 = wEU[i], y1 = wEV[i], x2 = wEU[j], y2 = wEV[j];
            if (x1 == x2 || y1 == y2) continue;
            if (has_nb(x1, y2) || has_nb(x2, y1)) continue;
            wEV[i] = y2;
            wEV[j] = y1;
            long long nc = eval_bad();
            long long dl = nc - cost;
            if (dl <= 0 || rnd01() < exp(-(double)dl / T)) {
                cost = nc;
            } else {
                wEV[i] = y1;
                wEV[j] = y2;
            }
        }
        if (cost == 0) continue;
        if (cost < epbest) {
            epbest = cost;
            stag = 0;
        } else {
            stag++;
        }
        if (stag >= STAG_EPOCHS) {
            restore_best();
            if (!augment()) break;
            cost = eval_bad();
            epbest = cost;
            stag = 0;
        }
    }
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

    /* Optional start graph on stdin. */
    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) {
        n0 = 0;
        m0 = 0;
    }
    if (n0 > 0 && m0 > 0) {
        int *su = malloc(sizeof(int) * (size_t)m0);
        int *sv = malloc(sizeof(int) * (size_t)m0);
        int okread = 1;
        for (int e = 0; e < m0; e++) {
            if (scanf("%d %d", &su[e], &sv[e]) != 2) {
                okread = 0;
                break;
            }
        }
        if (okread) {
            long long c = load_from(n0, m0, su, sv);
            if (c == 0) save_best();
        }
        free(su);
        free(sv);
    }

    /* Phase 1: bi-Cayley breakout search. */
    int req = min_n > BestN ? min_n : BestN;
    double until1 = t0 + tl * PHASE1_FRAC;
    Cfg bc;
    memset(&bc, 0, sizeof(bc));
    int bM = 1, bK = 1, bR = 1;
    if (now_s() < until1 - 0.5) {
        if (bicayley_phase(until1, req, &bc, &bM, &bK, &bR)) {
            int n = 0, m = 0;
            int *eu = NULL, *ev = NULL;
            cfg_edges(&bc, bM, bK, bR, &n, &m, &eu, &ev);
            long long c = load_from(n, m, eu, ev);
            if (c == 0 && n > BestN) save_best();
            free(eu);
            free(ev);
        }
    }

    /* Phase 2: vertex-pair insertion with annealing repair. */
    phase2(t0 + tl * END_FRAC);

    if (BestN == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", BestN, BestM);
    for (int e = 0; e < BestM; e++)
        printf("%d %d\n", BestEU[e], BestEV[e]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions first, then the C engine.
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

    # C engine: bi-Cayley search, then vertex-pair insertion with annealing repair.
    # The best construction is passed as the start graph.
    if d >= 3 and D >= 3:
        c_budget = deadline - time.monotonic() - 1.5
        if c_budget >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{c_budget:.2f}", best_n],
                                stdin_graph=best, timeout=time_limit - 3.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
