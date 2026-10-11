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
# C engine 1: bi-Cayley search with breakout local search (clause weighting),
# a unit-weight coordinate polish for near-solutions, and iterated local
# search. Used to secure a strong structured baseline.
# ----------------------------------------------------------------------------

C_BICAYLEY = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXD 64
#define MAXK 3
#define PEN 1000
#define POLISH_T 80
#define STUCK 50
#define BREAK_ITERS 25000
#define NEAR_PCT 50
#define PERTURB 3

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
# C engine 2 (new construction): unstructured graph-level annealing that GROWS
# a given graph. It adds vertex pairs (one per side) and then anneals over
# degree-preserving switches, degree-filling additions and "insert" moves
# (remove edge a1-b1, add a1-b2 and a2-b1 using spare degree at a2, b2).
# Cost = unreached pairs (distance > D) + 0.5 * spare degree. Bitset BFS.
# Any state with zero unreached pairs and degree <= d is a valid output.
# ----------------------------------------------------------------------------

SA_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2400
#define MAXD 32
#define WMAX ((MAXN + 63) / 64)

typedef struct {
    int nb[MAXN * MAXD];
    int deg[MAXN];
} St;

static St SA_, SB_, BEST;
static St *cur = &SA_, *cand = &SB_;
static int d = 3, D = 3, N = 0;
static int side[MAXN];
static uint64_t RA[MAXN * WMAX], RB[MAXN * WMAX];
static uint64_t rs = 0x9E3779B97F4A7C15ULL;
static const double DEFW = 0.5;
static const double T0 = 1.5, T1 = 0.05;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int n) { return (int)(rnd64() % (uint64_t)n); }

static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(const St *s, int u, int v) {
    const int *p = s->nb + u * d;
    for (int k = 0; k < s->deg[u]; k++)
        if (p[k] == v) return 1;
    return 0;
}

static void add_edge(St *s, int u, int v) {
    s->nb[u * d + s->deg[u]++] = v;
    s->nb[v * d + s->deg[v]++] = u;
}

static void del_one(St *s, int u, int v) {
    int *p = s->nb + u * d;
    int k = s->deg[u];
    for (int i = 0; i < k; i++) {
        if (p[i] == v) {
            p[i] = p[k - 1];
            s->deg[u] = k - 1;
            return;
        }
    }
}

static void rem_edge(St *s, int u, int v) {
    del_one(s, u, v);
    del_one(s, v, u);
}

/* Random vertex on side want_side; need_def: deg < d; else deg > 0. */
static int sample_side(const St *s, int want_side, int need_def) {
    int tries = need_def ? 3000 : 400;
    for (int t = 0; t < tries; t++) {
        int v = rint_(N);
        if (side[v] != want_side) continue;
        if (need_def) {
            if (s->deg[v] < d) return v;
        } else {
            if (s->deg[v] > 0) return v;
        }
    }
    return -1;
}

static int try_move(St *c) {
    int r = rint_(100);
    if (r < 25) {
        /* add an edge between two deficient vertices */
        int a = sample_side(c, 0, 1), b = sample_side(c, 1, 1);
        if (a < 0 || b < 0 || has_edge(c, a, b)) return 0;
        add_edge(c, a, b);
        return 1;
    }
    if (r < 50) {
        /* insert: remove a1-b1, add a1-b2 and a2-b1 (a2, b2 deficient) */
        int a1 = sample_side(c, 0, 0);
        if (a1 < 0) return 0;
        int b1 = c->nb[a1 * d + rint_(c->deg[a1])];
        int a2 = sample_side(c, 0, 1), b2 = sample_side(c, 1, 1);
        if (a2 < 0 || b2 < 0 || a2 == a1 || b2 == b1) return 0;
        if (has_edge(c, a2, b1) || has_edge(c, a1, b2)) return 0;
        rem_edge(c, a1, b1);
        add_edge(c, a1, b2);
        add_edge(c, a2, b1);
        return 1;
    }
    /* switch: degree-preserving double edge swap */
    int a1 = sample_side(c, 0, 0), a2 = sample_side(c, 0, 0);
    if (a1 < 0 || a2 < 0 || a1 == a2) return 0;
    int b1 = c->nb[a1 * d + rint_(c->deg[a1])];
    int b2 = c->nb[a2 * d + rint_(c->deg[a2])];
    if (b1 == b2 || has_edge(c, a1, b2) || has_edge(c, a2, b1)) return 0;
    rem_edge(c, a1, b1);
    rem_edge(c, a2, b2);
    add_edge(c, a1, b2);
    add_edge(c, a2, b1);
    return 1;
}

/* Returns number of unordered pairs at distance > D; *defc = spare degree. */
static long long evaluate(const St *s, long long *defc) {
    int Wn = (N + 63) >> 6;
    uint64_t *R0 = RA, *R1 = RB;
    memset(R0, 0, sizeof(uint64_t) * (size_t)N * (size_t)Wn);
    for (int v = 0; v < N; v++)
        R0[(size_t)v * Wn + (v >> 6)] |= 1ULL << (v & 63);
    for (int it = 0; it < D; it++) {
        for (int v = 0; v < N; v++) {
            uint64_t *dst = R1 + (size_t)v * Wn;
            const uint64_t *src = R0 + (size_t)v * Wn;
            memcpy(dst, src, sizeof(uint64_t) * (size_t)Wn);
            for (int k = 0; k < s->deg[v]; k++) {
                const uint64_t *o = R0 + (size_t)s->nb[v * d + k] * Wn;
                for (int w = 0; w < Wn; w++) dst[w] |= o[w];
            }
        }
        uint64_t *t = R0;
        R0 = R1;
        R1 = t;
    }
    long long cnt = 0;
    for (int v = 0; v < N; v++) {
        int pc = 0;
        const uint64_t *p = R0 + (size_t)v * Wn;
        for (int w = 0; w < Wn; w++) pc += popc(p[w]);
        cnt += N - pc;
    }
    long long def = 0;
    for (int v = 0; v < N; v++) def += d - s->deg[v];
    *defc = def;
    return cnt / 2;
}

/* Anneal the current state until it has no unreached pairs or time runs out. */
static int anneal(double end) {
    double t0 = now_s(), span = end - t0;
    if (span <= 0) return 0;
    long long def = 0;
    long long bad = evaluate(cur, &def);
    if (bad == 0) return 1;
    double cost = (double)bad + DEFW * (double)def;
    double T = T0;
    long it = 0;
    while (1) {
        if ((it & 31) == 0) {
            double t = now_s();
            if (t >= end) break;
            double f = (t - t0) / span;
            T = T0 * pow(T1 / T0, f);
        }
        it++;
        memcpy(cand->nb, cur->nb, sizeof(int) * (size_t)N * (size_t)d);
        memcpy(cand->deg, cur->deg, sizeof(int) * (size_t)N);
        if (!try_move(cand)) continue;
        long long def2 = 0;
        long long bad2 = evaluate(cand, &def2);
        double c2 = (double)bad2 + DEFW * (double)def2;
        double dc = c2 - cost;
        if (dc <= 0 || rnd01() < exp(-dc / T)) {
            St *tmp = cur;
            cur = cand;
            cand = tmp;
            cost = c2;
            bad = bad2;
            if (bad == 0) return 1;
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    d = argc > 1 ? atoi(argv[1]) : 3;
    D = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;
    if (d < 1 || d > MAXD || D < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 77ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();

    double deadline = now_s() + tl;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 < 1 || n0 > MAXN - 2 || m0 < 0) {
        printf("0 0\n");
        return 0;
    }
    memset(cur, 0, sizeof(St));
    N = n0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) {
            printf("0 0\n");
            return 0;
        }
        if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) {
            printf("0 0\n");
            return 0;
        }
        if (cur->deg[u] >= d || cur->deg[v] >= d) {
            printf("0 0\n");
            return 0;
        }
        if (has_edge(cur, u, v)) continue;
        add_edge(cur, u, v);
    }

    /* 2-colour the input graph. */
    for (int v = 0; v < N; v++) side[v] = -1;
    static int queue[MAXN];
    for (int s0 = 0; s0 < N; s0++) {
        if (side[s0] >= 0) continue;
        side[s0] = 0;
        int h = 0, t = 0;
        queue[t++] = s0;
        while (h < t) {
            int u = queue[h++];
            for (int k = 0; k < cur->deg[u]; k++) {
                int w = cur->nb[u * d + k];
                if (side[w] < 0) {
                    side[w] = 1 - side[u];
                    queue[t++] = w;
                } else if (side[w] == side[u]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }

    long long def0 = 0;
    if (evaluate(cur, &def0) != 0) {
        printf("0 0\n");
        return 0;
    }
    memcpy(&BEST, cur, sizeof(St));
    int bestN = N;

    while (1) {
        double now = now_s();
        double rem = deadline - now;
        if (rem < 0.5) break;
        if (N + 2 > MAXN) break;
        side[N] = 0;
        side[N + 1] = 1;
        cur->deg[N] = 0;
        cur->deg[N + 1] = 0;
        N += 2;
        double chunk = (rem > 6.0) ? 0.5 * rem : rem;
        if (anneal(now + chunk)) {
            memcpy(BEST.nb, cur->nb, sizeof(int) * (size_t)N * (size_t)d);
            memcpy(BEST.deg, cur->deg, sizeof(int) * (size_t)N);
            bestN = N;
        } else {
            N = bestN;
            memcpy(cur->nb, BEST.nb, sizeof(int) * (size_t)bestN * (size_t)d);
            memcpy(cur->deg, BEST.deg, sizeof(int) * (size_t)bestN);
        }
    }

    int m = 0;
    for (int v = 0; v < bestN; v++)
        if (side[v] == 0) m += BEST.deg[v];
    printf("%d %d\n", bestN, m);
    for (int v = 0; v < bestN; v++) {
        if (side[v] != 0) continue;
        for (int k = 0; k < BEST.deg[v]; k++)
            printf("%d %d\n", v, BEST.nb[v * d + k]);
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue.
# ----------------------------------------------------------------------------

def _search(d, D, seed, budget, min_n):
    """One bi-Cayley C search run. Returns (n, edges) if it produced a valid graph, else None."""
    try:
        out = lib.run_c(C_BICAYLEY, [d, D, seed, f"{budget:.2f}", min_n],
                        timeout=budget + 3.0)
        n, e = lib.parse_graph_text(out)
        if n > 0 and lib.is_valid(n, e, d, D):
            return n, e
    except Exception:
        pass
    return None


def _anneal(d, D, seed, graph, budget):
    """Grow a valid graph by annealing. Returns a larger valid (n, edges), else None."""
    try:
        out = lib.run_c(SA_SOURCE, [d, D, seed, f"{budget:.2f}"],
                        stdin_graph=graph, timeout=budget + 4.0)
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

    if d >= 3 and D >= 3:
        # Stage A: structured bi-Cayley search secures a strong baseline.
        total = deadline - time.monotonic() - 1.5
        if total >= 4.0:
            res1 = _search(d, D, seed, 0.4 * total, best_n)
            if res1 is not None:
                consider(*res1)
        # Stage B: unstructured annealing grows the best graph found so far.
        remaining = deadline - time.monotonic() - 1.5
        if remaining >= 2.0:
            res2 = _anneal(d, D, seed + 104729, best, remaining)
            if res2 is not None:
                consider(*res2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
