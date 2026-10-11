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
# C engine 1: bi-Cayley annealing with coordinate polish (group-lift family).
# Used for the first part of the budget to produce a strong starting graph.
# ----------------------------------------------------------------------------

C_GROUP = r'''
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
# C engine 2 (NEW, different construction): vertex insertion + degree-preserving
# edge-switch annealing on an arbitrary bipartite graph.
#
# Start from a valid bipartite graph. Insert two new vertices (one per side) by
# removing a matching of DEG edges and reattaching its endpoints to the new pair.
# Then anneal with bipartite double-edge swaps (A-B edges only, degrees kept),
# minimizing the number of ordered vertex pairs farther than DD apart (bitset
# ball computation). Whenever cost reaches 0 the state is snapshotted, so the
# output is always a valid graph.
# ----------------------------------------------------------------------------

C_REPAIR = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXV 2600
#define MAXDEG 16
#define MAXM (MAXV * MAXDEG / 2 + 1024)
#define WMAX 42

static uint64_t rs = 0x2545F4914F6CDD1DULL;

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

static int DEG = 3, DD = 3;
static int n_ = 0, m_ = 0;
static long cur_cost = 0;

static int side_[MAXV], dg_[MAXV];
static int nbr_[MAXV][MAXDEG];
static int eu_[MAXM], ev_[MAXM];   /* eu = A-side endpoint, ev = B-side endpoint */
static uint64_t bufA[MAXV * WMAX], bufB[MAXV * WMAX];
static int markA_[MAXV], markB_[MAXV];

static int snap_n = 0, snap_m = 0;
static int s_side[MAXV], s_dg[MAXV];
static int s_nbr[MAXV][MAXDEG];
static int s_eu[MAXM], s_ev[MAXM];

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    for (int t = 0; t < dg_[a]; t++)
        if (nbr_[a][t] == b) return 1;
    return 0;
}

static void repl(int v, int old, int nw) {
    for (int t = 0; t < dg_[v]; t++) {
        if (nbr_[v][t] == old) {
            nbr_[v][t] = nw;
            return;
        }
    }
}

/* Edges i=(a1,b1), j=(a2,b2) become (a1,b2), (a2,b1). Applying it twice undoes it. */
static void swap_edges(int i, int j) {
    int a1 = eu_[i], b1 = ev_[i], a2 = eu_[j], b2 = ev_[j];
    repl(a1, b1, b2);
    repl(b1, a1, a2);
    repl(a2, b2, b1);
    repl(b2, a2, a1);
    ev_[i] = b2;
    ev_[j] = b1;
}

static long cost_eval(void) {
    int n = n_, w = (n + 63) >> 6;
    uint64_t *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * (size_t)w);
    for (int v = 0; v < n; v++)
        cur[(size_t)v * w + (size_t)(v >> 6)] |= 1ULL << (v & 63);
    for (int s = 0; s < DD; s++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * w;
            const uint64_t *src = cur + (size_t)v * w;
            for (int k = 0; k < w; k++) dst[k] = src[k];
            for (int t = 0; t < dg_[v]; t++) {
                const uint64_t *u = cur + (size_t)nbr_[v][t] * w;
                for (int k = 0; k < w; k++) dst[k] |= u[k];
            }
        }
        uint64_t *tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    long unreached = 0;
    for (int v = 0; v < n; v++) {
        const uint64_t *r = cur + (size_t)v * w;
        int c = 0;
        for (int k = 0; k < w; k++) c += popc(r[k]);
        unreached += n - c;
    }
    return unreached;
}

static void save_snap(void) {
    snap_n = n_;
    snap_m = m_;
    memcpy(s_side, side_, sizeof(int) * (size_t)n_);
    memcpy(s_dg, dg_, sizeof(int) * (size_t)n_);
    memcpy(s_nbr, nbr_, sizeof(nbr_));
    memcpy(s_eu, eu_, sizeof(int) * (size_t)m_);
    memcpy(s_ev, ev_, sizeof(int) * (size_t)m_);
}

static void load_snap(void) {
    n_ = snap_n;
    m_ = snap_m;
    memcpy(side_, s_side, sizeof(int) * (size_t)n_);
    memcpy(dg_, s_dg, sizeof(int) * (size_t)n_);
    memcpy(nbr_, s_nbr, sizeof(nbr_));
    memcpy(eu_, s_eu, sizeof(int) * (size_t)m_);
    memcpy(ev_, s_ev, sizeof(int) * (size_t)m_);
}

static int read_input(void) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n < 2 || n > MAXV - 300 || m < 1 || m > MAXM - 1024) return 0;
    int *tu = malloc(sizeof(int) * (size_t)m);
    int *tv = malloc(sizeof(int) * (size_t)m);
    int *col = malloc(sizeof(int) * (size_t)n);
    int *queue = malloc(sizeof(int) * (size_t)n);
    if (!tu || !tv || !col || !queue) return 0;
    n_ = n;
    memset(dg_, 0, sizeof(dg_));
    int ok = 1;
    for (int i = 0; i < m && ok; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) { ok = 0; break; }
        if (has_edge(u, v)) { ok = 0; break; }
        if (dg_[u] >= DEG || dg_[v] >= DEG) { ok = 0; break; }
        nbr_[u][dg_[u]++] = v;
        nbr_[v][dg_[v]++] = u;
        tu[i] = u;
        tv[i] = v;
    }
    if (ok) {
        for (int v = 0; v < n; v++) col[v] = -1;
        for (int s = 0; s < n && ok; s++) {
            if (col[s] >= 0) continue;
            col[s] = 0;
            int head = 0, tail = 0;
            queue[tail++] = s;
            while (head < tail && ok) {
                int u = queue[head++];
                for (int t = 0; t < dg_[u]; t++) {
                    int v = nbr_[u][t];
                    if (col[v] < 0) {
                        col[v] = 1 - col[u];
                        queue[tail++] = v;
                    } else if (col[v] == col[u]) {
                        ok = 0;
                        break;
                    }
                }
            }
        }
    }
    if (ok) {
        for (int v = 0; v < n; v++) side_[v] = col[v];
        m_ = 0;
        for (int i = 0; i < m; i++) {
            int u = tu[i], v = tv[i];
            if (side_[u] == 0) {
                eu_[m_] = u;
                ev_[m_] = v;
            } else {
                eu_[m_] = v;
                ev_[m_] = u;
            }
            m_++;
        }
    }
    free(tu);
    free(tv);
    free(col);
    free(queue);
    return ok;
}

/* Insert a new A vertex (index n) and a new B vertex (index n+1). Remove a matching
   of DEG edges (x_k, y_k); add (A, y_k) and (x_k, B). Degrees are preserved. */
static int insert_pair(void) {
    int n = n_, A = n, B = n + 1;
    if (n + 2 > MAXV - 1 || m_ + DEG + 4 > MAXM) return 0;
    int chosen[MAXDEG];
    int cnt = 0;
    long tries = 0;
    while (cnt < DEG && tries < 400000) {
        tries++;
        int i = rint_(m_);
        int x = eu_[i], y = ev_[i];
        if (markA_[x] || markB_[y]) continue;
        markA_[x] = 1;
        markB_[y] = 1;
        chosen[cnt++] = i;
    }
    for (int k = 0; k < cnt; k++) {
        markA_[eu_[chosen[k]]] = 0;
        markB_[ev_[chosen[k]]] = 0;
    }
    if (cnt < DEG) return 0;
    side_[A] = 0;
    side_[B] = 1;
    dg_[A] = 0;
    dg_[B] = 0;
    for (int k = 0; k < cnt; k++) {
        int i = chosen[k];
        int x = eu_[i], y = ev_[i];
        repl(x, y, B);
        repl(y, x, A);
        eu_[i] = A;
        ev_[i] = y;
        eu_[m_] = x;
        ev_[m_] = B;
        m_++;
        nbr_[A][dg_[A]++] = y;
        nbr_[B][dg_[B]++] = x;
    }
    n_ = n + 2;
    return 1;
}

static void anneal_step(double T) {
    int i = rint_(m_), j = rint_(m_);
    if (i == j) return;
    int a1 = eu_[i], b1 = ev_[i], a2 = eu_[j], b2 = ev_[j];
    if (a1 == a2 || b1 == b2) return;
    if (has_edge(a1, b2) || has_edge(a2, b1)) return;
    swap_edges(i, j);
    long c = cost_eval();
    if (c <= cur_cost || rdbl() < exp(-(double)(c - cur_cost) / T)) {
        cur_cost = c;
    } else {
        swap_edges(i, j);
    }
}

int main(int argc, char **argv) {
    DEG = argc > 1 ? atoi(argv[1]) : 3;
    DD = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;

    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 777ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 4; w++) rnd();

    double deadline = now_s() + tl;
    if (DEG < 1 || DEG > MAXDEG || DD < 1 || !read_input()) {
        printf("0 0\n");
        return 0;
    }

    cur_cost = cost_eval();
    int have_snap = 0;
    if (cur_cost == 0) {
        save_snap();
        have_snap = 1;
    }

    const int ATT = 4000;
    int left = ATT;
    long it = 0;
    while (1) {
        if ((it & 63) == 0 && now_s() > deadline) break;
        it++;

        if (cur_cost == 0) {
            save_snap();
            have_snap = 1;
            if (!insert_pair()) break;
            cur_cost = cost_eval();
            left = ATT;
            continue;
        }

        if (left <= 0) {
            if (!have_snap) {
                left = ATT;
            } else {
                load_snap();
                if (!insert_pair()) break;
                cur_cost = cost_eval();
                left = ATT;
                continue;
            }
        }

        double frac = (double)left / (double)ATT;
        double T = 0.15 + 2.0 * frac;
        anneal_step(T);
        left--;
    }

    if (cur_cost == 0) {
        save_snap();
        have_snap = 1;
    }
    if (!have_snap) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", snap_n, snap_m);
    for (int i = 0; i < snap_m; i++) {
        printf("%d %d\n", s_eu[i], s_ev[i]);
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions, then group-lift search, then repair search.
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
        # Phase 1: group-lift annealing for a strong starting graph.
        left = deadline - time.monotonic()
        g_budget = 0.35 * left
        if g_budget >= 3.0:
            hard = time_limit - (time.monotonic() - start) - 2.0
            try:
                out = lib.run_c(C_GROUP, [d, D, seed, f"{g_budget:.2f}", best_n],
                                timeout=max(2.0, min(hard, g_budget + 20.0)))
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

        # Phase 2: insertion + edge-switch repair, starting from the best valid graph.
        left = deadline - time.monotonic()
        r_budget = left - 1.0
        if r_budget >= 3.0:
            hard = time_limit - (time.monotonic() - start) - 2.0
            try:
                out = lib.run_c(C_REPAIR, [d, D, seed, f"{r_budget:.2f}"],
                                stdin_graph=best,
                                timeout=max(2.0, min(hard, r_budget + 20.0)))
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
