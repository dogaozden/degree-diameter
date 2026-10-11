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
# Stage 1 C engine (parent): bi-Cayley search with breakout local search.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
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
    long long fails = 0;

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
            long long extra = fails / 40;
            if (extra > g0 / 10) extra = g0 / 10;
            span += extra;
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
            fails = 0;
        } else {
            if (!from_near) fails++;
            if (!have_near || g_rawcost <= nraw) {
                near = cur;
                nM = M;
                nK = Kk;
                nR = R;
                nraw = g_rawcost;
                have_near = 1;
            }
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
# Stage 2 C engine (new): vertex insertion with simulated-annealing repair.
# Input: a d-regular bipartite graph with diameter <= D (valid).
# Each step inserts two vertices x (side B) and y (side A): a matching of d
# edges a_i-b_i is removed, x joins all a_i and y joins all b_i. Degrees stay d.
# Then random 2-switches (a1-b1, a2-b2 -> a1-b2, a2-b1) anneal the number of
# vertex pairs at distance > D down to 0. Success grows the graph by 2.
# ----------------------------------------------------------------------------

INS_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXDEG 256
#define ATT_IT 4000
#define EXTRA_CAP 2000

static uint64_t rs = 0x9E3779B97F4A7C15ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }

static double rdouble(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int deg, DIAM;
static int n, cap;
static int *adj, *badj;
static unsigned char *side, *bside;
static int *Al, nA, *Bl, nB;
static uint64_t *bufA, *bufB;
static int base_n;
static int sa_a1, sa_s1, sa_a2, sa_s2, sa_b1, sa_b2;

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void rebuild_lists(void) {
    nA = 0;
    nB = 0;
    for (int v = 0; v < n; v++) {
        if (side[v] == 0) Al[nA++] = v;
        else Bl[nB++] = v;
    }
}

static void save_base(void) {
    memcpy(badj, adj, sizeof(int) * (size_t)n * (size_t)deg);
    memcpy(bside, side, (size_t)n);
    base_n = n;
}

static void restore_base(void) {
    memcpy(adj, badj, sizeof(int) * (size_t)base_n * (size_t)deg);
    memcpy(side, bside, (size_t)base_n);
    n = base_n;
    rebuild_lists();
}

/* Number of unordered vertex pairs at distance > DIAM (unreachable included). */
static long long cost_eval(void) {
    int N = n;
    int Wn = (N + 63) / 64;
    uint64_t *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N * (size_t)Wn);
    for (int v = 0; v < N; v++) cur[(size_t)v * Wn + (size_t)(v / 64)] |= 1ULL << (v % 64);
    for (int s = 0; s < DIAM; s++) {
        for (int v = 0; v < N; v++) {
            uint64_t *dst = nxt + (size_t)v * Wn;
            const uint64_t *src = cur + (size_t)v * Wn;
            memcpy(dst, src, sizeof(uint64_t) * (size_t)Wn);
            const int *row = adj + (size_t)v * deg;
            for (int t = 0; t < deg; t++) {
                const uint64_t *su = cur + (size_t)row[t] * Wn;
                for (int w = 0; w < Wn; w++) dst[w] |= su[w];
            }
        }
        uint64_t *tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    long long miss = 0;
    for (int v = 0; v < N; v++) {
        const uint64_t *r = cur + (size_t)v * Wn;
        int pc = 0;
        for (int w = 0; w < Wn; w++) pc += popc(r[w]);
        miss += (long long)(N - pc);
    }
    return miss / 2;
}

static int find_slot(int v, int w) {
    const int *row = adj + (size_t)v * deg;
    for (int t = 0; t < deg; t++)
        if (row[t] == w) return t;
    return -1;
}

static void replace_nb(int v, int old, int nw) {
    int t = find_slot(v, old);
    if (t >= 0) adj[(size_t)v * deg + t] = nw;
}

/* Random 2-switch: a1-b1, a2-b2 -> a1-b2, a2-b1. Keeps degrees and bipartiteness. */
static int do_switch(void) {
    if (nA < 2) return 0;
    int a1 = Al[rint_(nA)];
    int a2 = Al[rint_(nA)];
    if (a1 == a2) return 0;
    int s1 = rint_(deg), s2 = rint_(deg);
    int b1 = adj[(size_t)a1 * deg + s1];
    int b2 = adj[(size_t)a2 * deg + s2];
    if (b1 == b2) return 0;
    if (find_slot(a1, b2) >= 0 || find_slot(a2, b1) >= 0) return 0;
    adj[(size_t)a1 * deg + s1] = b2;
    adj[(size_t)a2 * deg + s2] = b1;
    replace_nb(b1, a1, a2);
    replace_nb(b2, a2, a1);
    sa_a1 = a1;
    sa_s1 = s1;
    sa_a2 = a2;
    sa_s2 = s2;
    sa_b1 = b1;
    sa_b2 = b2;
    return 1;
}

static void undo_switch(void) {
    adj[(size_t)sa_a1 * deg + sa_s1] = sa_b1;
    adj[(size_t)sa_a2 * deg + sa_s2] = sa_b2;
    replace_nb(sa_b1, sa_a2, sa_a1);
    replace_nb(sa_b2, sa_a1, sa_a2);
}

/* Insert two vertices: x (side B) takes a matching-compatible set of a_i,
   y (side A) takes the matched b_i; each edge a_i-b_i is replaced. */
static int insert_pair(void) {
    if (n + 2 > cap) return 0;
    int as_[MAXDEG], bs_[MAXDEG];
    int ok = 0;
    for (int tries = 0; tries < 500 && !ok; tries++) {
        int good = 1;
        for (int i = 0; i < deg && good; i++) {
            int a = Al[rint_(nA)];
            for (int j = 0; j < i; j++)
                if (as_[j] == a) { good = 0; break; }
            if (!good) break;
            int b = adj[(size_t)a * deg + rint_(deg)];
            for (int j = 0; j < i; j++)
                if (bs_[j] == b) { good = 0; break; }
            if (!good) break;
            as_[i] = a;
            bs_[i] = b;
        }
        ok = good;
    }
    if (!ok) return 0;
    int x = n, y = n + 1;
    side[x] = 1;
    side[y] = 0;
    for (int i = 0; i < deg; i++) {
        int a = as_[i], b = bs_[i];
        replace_nb(a, b, x);
        replace_nb(b, a, y);
        adj[(size_t)x * deg + i] = a;
        adj[(size_t)y * deg + i] = b;
    }
    n += 2;
    rebuild_lists();
    return 1;
}

static void print_graph_base(void) {
    int N = base_n;
    long m = 0;
    for (int v = 0; v < N; v++)
        if (bside[v] == 0) m += deg;
    printf("%d %ld\n", N, m);
    for (int v = 0; v < N; v++) {
        if (bside[v] != 0) continue;
        for (int t = 0; t < deg; t++)
            printf("%d %d\n", v, badj[(size_t)v * deg + t]);
    }
}

static void print_input(int n0, int m0, const int *eu, const int *ev) {
    printf("%d %d\n", n0, m0);
    for (int i = 0; i < m0; i++) printf("%d %d\n", eu[i], ev[i]);
}

int main(int argc, char **argv) {
    int d = argc > 1 ? atoi(argv[1]) : 3;
    DIAM = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 777ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 8; w++) rnd();

    double deadline = now_s() + tl;
    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 <= 0 || m0 < 0) {
        printf("0 0\n");
        return 0;
    }
    if (d < 1 || d > MAXDEG || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    deg = d;
    int *eu = malloc(sizeof(int) * (size_t)(m0 > 0 ? m0 : 1));
    int *ev = malloc(sizeof(int) * (size_t)(m0 > 0 ? m0 : 1));
    if (!eu || !ev) {
        printf("0 0\n");
        return 0;
    }
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) {
            printf("0 0\n");
            return 0;
        }
        if (eu[i] < 0 || eu[i] >= n0 || ev[i] < 0 || ev[i] >= n0 || eu[i] == ev[i]) {
            printf("0 0\n");
            return 0;
        }
    }

    int *cnt = calloc((size_t)n0, sizeof(int));
    for (int i = 0; i < m0; i++) {
        cnt[eu[i]]++;
        cnt[ev[i]]++;
    }
    int regular = 1;
    for (int v = 0; v < n0; v++)
        if (cnt[v] != deg) regular = 0;
    if (!regular) {
        print_input(n0, m0, eu, ev);
        return 0;
    }

    cap = n0 + EXTRA_CAP;
    int Wcap = (cap + 63) / 64;
    adj = malloc(sizeof(int) * (size_t)cap * (size_t)deg);
    badj = malloc(sizeof(int) * (size_t)cap * (size_t)deg);
    side = malloc((size_t)cap);
    bside = malloc((size_t)cap);
    Al = malloc(sizeof(int) * (size_t)cap);
    Bl = malloc(sizeof(int) * (size_t)cap);
    bufA = malloc(sizeof(uint64_t) * (size_t)cap * (size_t)Wcap);
    bufB = malloc(sizeof(uint64_t) * (size_t)cap * (size_t)Wcap);
    if (!adj || !badj || !side || !bside || !Al || !Bl || !bufA || !bufB) {
        fprintf(stderr, "out of memory\n");
        return 1;
    }

    /* Build adjacency and check bipartiteness. */
    int *fill = calloc((size_t)n0, sizeof(int));
    for (int i = 0; i < m0; i++) {
        int u = eu[i], v = ev[i];
        adj[(size_t)u * deg + fill[u]++] = v;
        adj[(size_t)v * deg + fill[v]++] = u;
    }
    for (int v = 0; v < cap; v++) side[v] = 0;
    int *color = malloc(sizeof(int) * (size_t)n0);
    int *queue = malloc(sizeof(int) * (size_t)n0);
    for (int v = 0; v < n0; v++) color[v] = -1;
    int bip = 1;
    for (int s = 0; s < n0 && bip; s++) {
        if (color[s] != -1) continue;
        int head = 0, tail = 0;
        color[s] = 0;
        queue[tail++] = s;
        while (head < tail && bip) {
            int u = queue[head++];
            for (int t = 0; t < deg; t++) {
                int v = adj[(size_t)u * deg + t];
                if (color[v] == -1) {
                    color[v] = 1 - color[u];
                    queue[tail++] = v;
                } else if (color[v] == color[u]) {
                    bip = 0;
                    break;
                }
            }
        }
    }
    if (!bip) {
        print_input(n0, m0, eu, ev);
        return 0;
    }
    n = n0;
    for (int v = 0; v < n0; v++) side[v] = (unsigned char)color[v];
    rebuild_lists();
    save_base();

    /* The start graph must already satisfy the diameter bound. */
    if (cost_eval() != 0) {
        print_input(n0, m0, eu, ev);
        return 0;
    }
    save_base();

    while (now_s() < deadline) {
        restore_base();
        if (!insert_pair()) continue;
        long long cost = cost_eval();
        for (int it = 0; it < ATT_IT && cost > 0; it++) {
            if ((it & 31) == 0 && now_s() > deadline) break;
            double T = 2.0 * (1.0 - (double)it / (double)ATT_IT) + 0.1;
            if (!do_switch()) continue;
            long long c2 = cost_eval();
            long long delta = c2 - cost;
            if (delta <= 0 || rdouble() < exp(-(double)delta / T)) {
                cost = c2;
            } else {
                undo_switch();
            }
        }
        if (cost == 0) save_base();
    }

    print_graph_base();
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue.
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

    # Already at the Moore bound: nothing can beat it.
    if best_n >= lib.moore_bound(d, D):
        return best

    # Stage 1: bi-Cayley search in C (parent engine), with a share of the budget.
    if d >= 3 and D >= 3:
        remaining = deadline - time.monotonic()
        b1 = 0.40 * remaining
        if b1 >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{b1:.2f}", best_n],
                                timeout=b1 + 4.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    # Stage 2: vertex insertion with annealing repair, starting from the best valid graph.
    if d >= 3 and D >= 3 and best_n > 2:
        remaining = deadline - time.monotonic() - 1.0
        if remaining >= 2.0:
            try:
                out = lib.run_c(INS_SOURCE, [d, D, seed, f"{remaining:.2f}"],
                                stdin_graph=best, timeout=remaining + 4.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
