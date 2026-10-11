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
# Stage 1 C engine (group-lift search, from the parent): bi-Cayley search with
# breakout local search, coordinate polish, and iterated local search.
# ----------------------------------------------------------------------------

C_SOURCE_GROUP = r'''
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
# Stage 2 C engine (new): non-group repair-and-grow search. It starts from a
# valid bipartite graph of max degree d and diameter D, adds vertex pairs
# when the graph is valid, and repairs with simulated annealing over
# generic edge insertions and 2-switches. Cost = number of vertex pairs at
# distance > D, computed by bitset BFS. The best valid graph is printed.
# ----------------------------------------------------------------------------

C_SOURCE_GROW = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define MAXDEG 64
#define NMAX 8000
#define WMAX 125

static int d = 3, D = 3, n = 0;
static int adj[NMAX][MAXDEG];
static int deg[NMAX];
static int col[NMAX];
static int listA[NMAX], listB[NMAX];
static int nA = 0, nB = 0;
static uint64_t RA[NMAX * WMAX], RB[NMAX * WMAX];
static int best_e[NMAX * MAXDEG];
static int best_n = -1, best_m = 0;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int k) { return (int)(rnd() % (uint64_t)k); }

static double rand01(void) {
    return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0);
}

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static long long bad_pairs(void) {
    int W = (n + 63) >> 6;
    uint64_t *cur = RA, *nxt = RB;
    for (int v = 0; v < n; v++) {
        memset(cur + (size_t)v * W, 0, sizeof(uint64_t) * (size_t)W);
        cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            memcpy(dst, cur + (size_t)v * W, sizeof(uint64_t) * (size_t)W);
            for (int t = 0; t < deg[v]; t++) {
                const uint64_t *src = cur + (size_t)adj[v][t] * W;
                for (int w = 0; w < W; w++) dst[w] |= src[w];
            }
        }
        uint64_t *tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *row = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(row[w]);
        bad += (long long)(n - c);
    }
    return bad / 2;
}

static int has_edge(int a, int b) {
    for (int t = 0; t < deg[a]; t++)
        if (adj[a][t] == b) return 1;
    return 0;
}

static void del_one(int a, int b) {
    for (int t = 0; t < deg[a]; t++) {
        if (adj[a][t] == b) {
            adj[a][t] = adj[a][--deg[a]];
            return;
        }
    }
}

static void del_edge(int a, int b) {
    del_one(a, b);
    del_one(b, a);
}

static void add_edge(int a, int b) {
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}

typedef struct {
    int np, na;
    int p[2][2];
    int a[2][2];
} Move;

static int propose(Move *m) {
    m->np = 0;
    m->na = 0;
    if (rint_(2) == 0) {
        int x = listA[rint_(nA)];
        int y = listB[rint_(nB)];
        if (has_edge(x, y)) return 0;
        if (deg[x] >= d) {
            int z = adj[x][rint_(deg[x])];
            m->p[m->np][0] = x;
            m->p[m->np][1] = z;
            m->np++;
        }
        if (deg[y] >= d) {
            int w = adj[y][rint_(deg[y])];
            m->p[m->np][0] = w;
            m->p[m->np][1] = y;
            m->np++;
        }
        m->a[0][0] = x;
        m->a[0][1] = y;
        m->na = 1;
        return 1;
    } else {
        int a = listA[rint_(nA)];
        if (deg[a] == 0) return 0;
        int b = adj[a][rint_(deg[a])];
        int c = listA[rint_(nA)];
        if (deg[c] == 0) return 0;
        int e = adj[c][rint_(deg[c])];
        if (a == c || b == e) return 0;
        if (has_edge(a, e) || has_edge(c, b)) return 0;
        m->p[0][0] = a;
        m->p[0][1] = b;
        m->p[1][0] = c;
        m->p[1][1] = e;
        m->np = 2;
        m->a[0][0] = a;
        m->a[0][1] = e;
        m->a[1][0] = c;
        m->a[1][1] = b;
        m->na = 2;
        return 1;
    }
}

static void apply_move(const Move *m) {
    for (int i = 0; i < m->np; i++) del_edge(m->p[i][0], m->p[i][1]);
    for (int i = 0; i < m->na; i++) add_edge(m->a[i][0], m->a[i][1]);
}

static void undo_move(const Move *m) {
    for (int i = 0; i < m->na; i++) del_edge(m->a[i][0], m->a[i][1]);
    for (int i = 0; i < m->np; i++) add_edge(m->p[i][0], m->p[i][1]);
}

static void save_best(void) {
    int k = 0;
    for (int i = 0; i < nA; i++) {
        int a = listA[i];
        for (int t = 0; t < deg[a]; t++) {
            best_e[k++] = a;
            best_e[k++] = adj[a][t];
        }
    }
    best_m = k / 2;
    best_n = n;
}

static void add_pair(void) {
    int x = n++;
    int y = n++;
    deg[x] = 0;
    deg[y] = 0;
    col[x] = 0;
    col[y] = 1;
    listA[nA++] = x;
    listB[nB++] = y;
    add_edge(x, y);
}

static int coloring(void) {
    for (int v = 0; v < n; v++) col[v] = -1;
    int *q = malloc(sizeof(int) * (size_t)(n > 0 ? n : 1));
    if (!q) return 0;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        int h = 0, t = 0;
        col[s] = 0;
        q[t++] = s;
        while (h < t) {
            int u = q[h++];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[u][k];
                if (col[v] < 0) {
                    col[v] = 1 - col[u];
                    q[t++] = v;
                } else if (col[v] == col[u]) {
                    free(q);
                    return 0;
                }
            }
        }
    }
    free(q);
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    if (d < 1 || d > MAXDEG || D < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 987654321ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 4; w++) rnd();

    double t0 = now_s();
    double deadline = t0 + tl;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 <= 0 || n0 > NMAX || m0 < 0) {
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
            printf("0 0\n");
            return 0;
        }
    }
    n = n0;
    memset(deg, 0, sizeof(deg));
    for (int i = 0; i < m0; i++) {
        int u = eu[i], v = ev[i];
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) {
            printf("0 0\n");
            return 0;
        }
        if (deg[u] >= d || deg[v] >= d || has_edge(u, v)) {
            printf("0 0\n");
            return 0;
        }
        add_edge(u, v);
    }
    if (!coloring()) {
        printf("0 0\n");
        return 0;
    }
    nA = nB = 0;
    for (int v = 0; v < n; v++) {
        if (col[v] == 0) listA[nA++] = v;
        else listB[nB++] = v;
    }
    if (nA == 0 || nB == 0) {
        printf("0 0\n");
        return 0;
    }

    long long cur = bad_pairs();
    if (cur == 0) save_best();

    double T = 1.0;
    Move mv;
    long it = 0;
    while (1) {
        if ((it & 63) == 0 && now_s() > deadline) break;
        it++;
        if (cur == 0) {
            save_best();
            if (n + 2 > NMAX) break;
            add_pair();
            cur = bad_pairs();
            continue;
        }
        if (!propose(&mv)) continue;
        apply_move(&mv);
        long long nb = bad_pairs();
        long long delta = nb - cur;
        if (delta <= 0 || rand01() < exp(-(double)delta / T)) {
            cur = nb;
        } else {
            undo_move(&mv);
        }
    }

    if (best_n < 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++)
        printf("%d %d\n", best_e[2 * i], best_e[2 * i + 1]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions, then stage 1 (group search), then stage 2
# (non-group repair-and-grow) started from the best valid graph so far.
# ----------------------------------------------------------------------------

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

    if d < 3 or D < 3:
        return best

    # Stage 1: group-lift search (about 40% of the remaining time).
    rem = deadline - time.monotonic()
    b1 = 0.40 * rem
    if b1 >= 2.0:
        try:
            out = lib.run_c(C_SOURCE_GROUP, [d, D, seed, f"{b1:.2f}", best_n],
                            timeout=b1 + 3.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    # Stage 2: repair-and-grow from the best valid graph found so far.
    rem = deadline - time.monotonic() - 1.0
    if rem >= 2.0:
        try:
            out = lib.run_c(C_SOURCE_GROW, [d, D, seed + 1, f"{rem:.2f}"],
                            stdin_graph=best, timeout=rem + 3.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
