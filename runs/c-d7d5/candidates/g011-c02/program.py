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


def _is_regular(n, edges, d):
    """True if every vertex of the graph has degree exactly d."""
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    return all(x == d for x in deg)


# ----------------------------------------------------------------------------
# C engine 1: bi-Cayley annealing (parent search, unchanged).
# ----------------------------------------------------------------------------

C_SOURCE_BICAYLEY = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 64
#define MAXK 3
#define PEN 1000
#define POLISH_T 80

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

static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int Dd = 3, DD = 3;
static int GM = 1, GK = 1, GG = 1;
static int gpow[64];
static double deadline = 0.0;
static int ITERS = 40000;

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
static int g_stamp = 0;

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
'''


# ----------------------------------------------------------------------------
# C engine 2 (NEW): switch-based growth on an arbitrary d-regular bipartite graph.
#
# Start from a valid d-regular bipartite graph H on N vertices. Each growth step:
#   * insert two new vertices x (side A) and y (side B) by removing a matching
#     (a_i, b_i), i = 1..d, and joining x to every b_i and y to every a_i.
#     Degrees stay exactly d and the graph stays bipartite and regular.
#   * repair by simulated annealing over degree-preserving 2-switches
#     (a,b),(c,e) -> (a,e),(c,b), with cost = number of unordered vertex pairs at
#     distance > D. Distances come from bitset ball expansion.
#   * on success, the valid N+2 vertex graph becomes the new base.
# Outputs the largest valid graph found, in "n m" + "u v" format.
# ----------------------------------------------------------------------------

C_SOURCE_SWITCH = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXV 4200
#define MAXDEG 24
#define MAXW 80

static int d_ = 3, D_ = 3;
static int N = 0;
static int adj[MAXV][MAXDEG];
static int col[MAXV];
static int adjB[MAXV][MAXDEG];
static int colB[MAXV];
static int NB = 0;
static uint64_t BA[MAXV][MAXW];
static uint64_t BB[MAXV][MAXW];
static uint64_t rs = 88172645463325252ULL;
static double deadline = 0.0;
static double T0 = 1.2;
static long LIM = 2500;

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

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of unordered pairs at distance > D_ (unreachable counts too). */
static long cost_bad(void) {
    int W = (N + 63) >> 6;
    uint64_t (*cur)[MAXW] = BA;
    uint64_t (*nxt)[MAXW] = BB;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < W; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < D_; r++) {
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = cur[v][w];
            for (int k = 0; k < d_; k++) {
                int u = adj[v][k];
                for (int w = 0; w < W; w++) nxt[v][w] |= cur[u][w];
            }
        }
        uint64_t (*t)[MAXW] = cur;
        cur = nxt;
        nxt = t;
    }
    long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(cur[v][w]);
        bad += N - c;
    }
    return bad / 2;
}

static int has_edge(int u, int v) {
    for (int k = 0; k < d_; k++)
        if (adj[u][k] == v) return 1;
    return 0;
}

static void sw_fix(int X, int a, int c) {
    for (int k = 0; k < d_; k++)
        if (adj[X][k] == a) {
            adj[X][k] = c;
            return;
        }
}

/* Switch: adj[a][ia] = X, adj[c][ic] = Y  ->  adj[a][ia] = Y, adj[c][ic] = X.
   Calling it again with the same indices undoes the switch. */
static void do_switch(int a, int ia, int c, int ic) {
    int X = adj[a][ia], Y = adj[c][ic];
    adj[a][ia] = Y;
    adj[c][ic] = X;
    sw_fix(X, a, c);
    sw_fix(Y, c, a);
}

static int propose(int *a, int *ia, int *c, int *ic) {
    for (int tries = 0; tries < 1000; tries++) {
        int x = rint_(N), y = rint_(N);
        if (x == y || col[x] != 0 || col[y] != 0) continue;
        int k = rint_(d_), l = rint_(d_);
        int b = adj[x][k], e = adj[y][l];
        if (b == e) continue;
        if (has_edge(x, e) || has_edge(y, b)) continue;
        *a = x;
        *ia = k;
        *c = y;
        *ic = l;
        return 1;
    }
    return 0;
}

static int run_sa(long lim) {
    long cost = cost_bad();
    for (long t = 0; t < lim && cost > 0; t++) {
        if ((t & 63) == 0 && now_s() > deadline) return 0;
        double T = T0 * (1.0 - (double)t / (double)lim) + 0.05;
        int a, ia, c, ic;
        if (!propose(&a, &ia, &c, &ic)) continue;
        do_switch(a, ia, c, ic);
        long c2 = cost_bad();
        long dl = c2 - cost;
        if (dl <= 0 || rdbl() < exp(-(double)dl / T))
            cost = c2;
        else
            do_switch(a, ia, c, ic);
    }
    return cost == 0;
}

static int insert_two(void) {
    int As[MAXDEG], Bs[MAXDEG];
    int cnt = 0;
    long tries = 0;
    if (N + 2 > MAXV) return 0;
    while (cnt < d_ && tries < 200000) {
        tries++;
        int a = rint_(N);
        if (col[a] != 0) continue;
        int b = adj[a][rint_(d_)];
        int dup = 0;
        for (int i = 0; i < cnt; i++)
            if (As[i] == a || Bs[i] == b) {
                dup = 1;
                break;
            }
        if (dup) continue;
        As[cnt] = a;
        Bs[cnt] = b;
        cnt++;
    }
    if (cnt < d_) return 0;
    int x = N, y = N + 1;
    col[x] = 0;
    col[y] = 1;
    for (int i = 0; i < d_; i++) {
        int a = As[i], b = Bs[i];
        for (int k = 0; k < d_; k++)
            if (adj[a][k] == b) {
                adj[a][k] = y;
                break;
            }
        for (int k = 0; k < d_; k++)
            if (adj[b][k] == a) {
                adj[b][k] = x;
                break;
            }
        adj[x][i] = b;
        adj[y][i] = a;
    }
    N += 2;
    return 1;
}

static void save_best(void) {
    NB = N;
    memcpy(adjB, adj, sizeof(int) * (size_t)N * MAXDEG);
    memcpy(colB, col, sizeof(int) * (size_t)N);
}

static void restore_best(void) {
    N = NB;
    memcpy(adj, adjB, sizeof(int) * (size_t)N * MAXDEG);
    memcpy(col, colB, sizeof(int) * (size_t)N);
}

static void output_best(void) {
    long cnt = 0;
    for (int v = 0; v < NB; v++)
        if (colB[v] == 0) cnt += d_;
    printf("%d %ld\n", NB, cnt);
    for (int v = 0; v < NB; v++) {
        if (colB[v] != 0) continue;
        for (int k = 0; k < d_; k++)
            printf("%d %d\n", v, adjB[v][k]);
    }
}

int main(int argc, char **argv) {
    d_ = argc > 1 ? atoi(argv[1]) : 3;
    D_ = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;

    if (d_ < 2 || d_ > MAXDEG || D_ < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 987654321ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 4; w++) rnd();

    double t0 = now_s();
    deadline = t0 + tl;

    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n < 2 || n > MAXV - 2 || m < 0) {
        printf("0 0\n");
        return 0;
    }
    static int deg[MAXV];
    memset(deg, 0, sizeof(deg));
    int bad = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) {
            bad = 1;
            break;
        }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v || deg[u] >= d_ || deg[v] >= d_) {
            bad = 1;
            continue;
        }
        adj[u][deg[u]++] = v;
        adj[v][deg[v]++] = u;
    }
    if (bad) {
        printf("0 0\n");
        return 0;
    }
    for (int v = 0; v < n; v++)
        if (deg[v] != d_) bad = 1;
    if (bad) {
        printf("0 0\n");
        return 0;
    }
    /* duplicate-edge check */
    for (int v = 0; v < n && !bad; v++)
        for (int k = 0; k < d_ && !bad; k++)
            for (int k2 = k + 1; k2 < d_; k2++)
                if (adj[v][k] == adj[v][k2]) {
                    bad = 1;
                    break;
                }
    if (bad) {
        printf("0 0\n");
        return 0;
    }
    /* bipartition by BFS */
    for (int v = 0; v < n; v++) col[v] = -1;
    static int stk[MAXV];
    for (int s = 0; s < n && !bad; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp > 0 && !bad) {
            int u = stk[--sp];
            for (int k = 0; k < d_; k++) {
                int v = adj[u][k];
                if (col[v] < 0) {
                    col[v] = 1 - col[u];
                    stk[sp++] = v;
                } else if (col[v] == col[u]) {
                    bad = 1;
                    break;
                }
            }
        }
    }
    if (bad) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    if (cost_bad() != 0) {
        printf("0 0\n");
        return 0;
    }
    save_best();

    long fails = 0;
    while (now_s() < deadline && N + 2 <= MAXV) {
        restore_best();
        if (!insert_two()) {
            fails++;
            if (fails > 100000) break;
            continue;
        }
        if (run_sa(LIM)) {
            save_best();
            fails = 0;
        }
    }
    output_best();
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions, then bi-Cayley search, then switch growth.
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

    if d >= 3 and D >= 3:
        # Stage 1: bi-Cayley annealing from scratch (lower bound best_n).
        remaining = deadline - time.monotonic()
        b1 = 0.45 * remaining
        if b1 >= 2.0:
            try:
                out = lib.run_c(C_SOURCE_BICAYLEY, [d, D, seed, f"{b1:.2f}", best_n],
                                timeout=b1 + 4.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

        # Stage 2: grow the best d-regular graph by switch-repaired vertex insertion.
        remaining = deadline - time.monotonic() - 1.0
        if remaining >= 3.0:
            if _is_regular(best[0], best[1], d):
                seed_graph = best
            else:
                seed_graph = lib.haar_graph(d, range(d))
            b2 = remaining
            try:
                out = lib.run_c(C_SOURCE_SWITCH, [d, D, seed + 7, f"{b2:.2f}"],
                                stdin_graph=seed_graph, timeout=b2 + 4.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
