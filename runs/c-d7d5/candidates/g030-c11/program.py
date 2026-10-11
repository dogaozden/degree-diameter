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
# search. Vertices: A_{i,g} = i*G+g, B_{j,h} = (K+j)*G+h, dart (l, i) joins
# A_{i,g} to B_{P[l][i], g*S[l][i]}.
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
# C engine 2 (new): grow-and-repair on general bipartite graphs.
#
# A bipartite graph is kept with degree <= d. The objective is the number of
# unordered vertex pairs at distance > D (bitset balls). Moves are degree-
# preserving 2-switches (a-b, c-d -> a-d, c-b), accepted by annealing.
# Growth step ("surgery"): from a valid graph on n vertices, delete d edges
# x_i-y_i with distinct endpoints, add a' (side A) joined to all y_i and
# b' (side B) joined to all x_i. This gives n+2 vertices with all degrees d,
# then annealing repairs the diameter. Without an input graph, the engine
# starts from a random bi-circulant d-regular graph of the target order.
# ----------------------------------------------------------------------------

REPAIR_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 4352
#define MAXW 68
#define MAXDEG 32
#define CHUNK 1500

static int Dd = 7, DD = 5;
static int N = 0, W = 1;
static int deg_[MAXN];
static int adj[MAXN][MAXDEG];
static int side[MAXN];
static int listS[2][MAXN];
static int nS[2];
static uint64_t bA[MAXN][MAXW], bB[MAXN][MAXW];
static int cb_adj[MAXN][MAXDEG];
static int cb_deg[MAXN];
static uint64_t rs = 88172645463325252ULL;
static double deadline = 0.0;

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

static inline int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void rebuild_lists(void) {
    nS[0] = 0;
    nS[1] = 0;
    for (int v = 0; v < N; v++) listS[side[v]][nS[side[v]]++] = v;
    W = (N + 63) / 64;
}

static int has_edge(int a, int b) {
    for (int t = 0; t < deg_[a]; t++)
        if (adj[a][t] == b) return 1;
    return 0;
}

static int find_idx(int a, int b) {
    for (int t = 0; t < deg_[a]; t++)
        if (adj[a][t] == b) return t;
    return -1;
}

static void remove_from(int v, int u) {
    for (int t = 0; t < deg_[v]; t++) {
        if (adj[v][t] == u) {
            adj[v][t] = adj[v][deg_[v] - 1];
            deg_[v]--;
            return;
        }
    }
}

/* Number of unordered pairs at distance > DD (unreached pairs). */
static long long bad_count(void) {
    uint64_t (*R)[MAXW] = bA, (*Q)[MAXW] = bB;
    int w = W;
    for (int v = 0; v < N; v++) {
        memset(R[v], 0, sizeof(uint64_t) * (size_t)w);
        R[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int s = 0; s < DD; s++) {
        for (int v = 0; v < N; v++) {
            uint64_t *q = Q[v];
            memcpy(q, R[v], sizeof(uint64_t) * (size_t)w);
            for (int t = 0; t < deg_[v]; t++) {
                const uint64_t *r = R[adj[v][t]];
                for (int k = 0; k < w; k++) q[k] |= r[k];
            }
        }
        uint64_t (*tmp)[MAXW] = R;
        R = Q;
        Q = tmp;
    }
    long long unr = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int k = 0; k < w; k++) c += pc64(R[v][k]);
        unr += N - c;
    }
    return unr / 2;
}

static int us_v[4], us_deg[4], us_row[4][MAXDEG];

static void save_row(int i, int v) {
    us_v[i] = v;
    us_deg[i] = deg_[v];
    memcpy(us_row[i], adj[v], sizeof(int) * (size_t)deg_[v]);
}

static void restore_rows(void) {
    for (int i = 0; i < 4; i++) {
        int v = us_v[i];
        deg_[v] = us_deg[i];
        memcpy(adj[v], us_row[i], sizeof(int) * (size_t)us_deg[i]);
    }
}

/* Random bipartite 2-switch. Returns 1 if applied (undo with restore_rows). */
static int try_switch(void) {
    if (nS[0] < 2 || nS[1] < 2) return 0;
    int a = listS[0][rint_(nS[0])];
    int c = listS[0][rint_(nS[0])];
    if (a == c || deg_[a] == 0 || deg_[c] == 0) return 0;
    int ka = rint_(deg_[a]);
    int b = adj[a][ka];
    int kc = rint_(deg_[c]);
    int d = adj[c][kc];
    if (b == d) return 0;
    if (has_edge(a, d) || has_edge(c, b)) return 0;
    save_row(0, a);
    save_row(1, b);
    save_row(2, c);
    save_row(3, d);
    int ib = find_idx(b, a);
    int id = find_idx(d, c);
    adj[a][ka] = d;
    adj[b][ib] = c;
    adj[c][kc] = b;
    adj[d][id] = a;
    return 1;
}

static void save_to(int (*A)[MAXDEG], int *D) {
    memcpy(A, adj, sizeof(int) * (size_t)N * MAXDEG);
    memcpy(D, deg_, sizeof(int) * (size_t)N);
}

static void load_from(int (*A)[MAXDEG], int *D) {
    memcpy(adj, A, sizeof(int) * (size_t)N * MAXDEG);
    memcpy(deg_, D, sizeof(int) * (size_t)N);
}

/* Simulated annealing on bad_count; leaves the graph at the chunk's best state. */
static long long anneal(long iters, double T0, double T1) {
    long long cur = bad_count();
    long long best = cur;
    save_to(cb_adj, cb_deg);
    double ratio = pow(T1 / T0, 1.0 / (double)iters);
    double T = T0;
    for (long it = 0; it < iters && best > 0; it++) {
        if ((it & 31) == 0 && now_s() > deadline) break;
        T *= ratio;
        if (!try_switch()) continue;
        long long nc = bad_count();
        long long delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = nc;
            if (cur < best) {
                best = cur;
                save_to(cb_adj, cb_deg);
            }
        } else {
            restore_rows();
        }
    }
    load_from(cb_adj, cb_deg);
    rebuild_lists();
    return best;
}

static int mkx[MAXN], mky[MAXN];
static int mstamp = 0;

/* Surgery: add two vertices (side 0 = a2, side 1 = b2), each of degree Dd. */
static int grow(void) {
    if (N + 2 > MAXN - 2 || nS[0] == 0) return 0;
    mstamp++;
    int ex[MAXDEG], ey[MAXDEG], ne = 0;
    int off = rint_(nS[0]);
    for (int s = 0; s < nS[0] && ne < Dd; s++) {
        int x = listS[0][(off + s) % nS[0]];
        if (mkx[x] == mstamp || deg_[x] == 0) continue;
        int k0 = rint_(deg_[x]);
        for (int t = 0; t < deg_[x]; t++) {
            int y = adj[x][(k0 + t) % deg_[x]];
            if (mky[y] == mstamp) continue;
            mkx[x] = mstamp;
            mky[y] = mstamp;
            ex[ne] = x;
            ey[ne] = y;
            ne++;
            break;
        }
    }
    if (ne < Dd) return 0;
    int a2 = N, b2 = N + 1;
    side[a2] = 0;
    side[b2] = 1;
    deg_[a2] = 0;
    deg_[b2] = 0;
    for (int i = 0; i < ne; i++) {
        int x = ex[i], y = ey[i];
        remove_from(x, y);
        remove_from(y, x);
        adj[x][deg_[x]++] = b2;
        adj[y][deg_[y]++] = a2;
        adj[a2][deg_[a2]++] = y;
        adj[b2][deg_[b2]++] = x;
    }
    N += 2;
    rebuild_lists();
    return 1;
}

/* Random bi-circulant d-regular bipartite graph on 2h vertices. */
static void build_circ(int h) {
    N = 2 * h;
    for (int v = 0; v < N; v++) {
        deg_[v] = 0;
        side[v] = v < h ? 0 : 1;
    }
    int sh[MAXDEG], ns = 0;
    while (ns < Dd) {
        int s = rint_(h), dup = 0;
        for (int i = 0; i < ns; i++)
            if (sh[i] == s) dup = 1;
        if (!dup) sh[ns++] = s;
    }
    for (int i = 0; i < h; i++) {
        for (int k = 0; k < Dd; k++) {
            int j = (i + sh[k]) % h;
            adj[i][deg_[i]++] = h + j;
            adj[h + j][deg_[h + j]++] = i;
        }
    }
    rebuild_lists();
}

static int color_graph(void) {
    static int q[MAXN];
    for (int v = 0; v < N; v++) side[v] = -1;
    for (int s = 0; s < N; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int v = q[h++];
            for (int k = 0; k < deg_[v]; k++) {
                int u = adj[v][k];
                if (side[u] < 0) {
                    side[u] = 1 - side[v];
                    q[t++] = u;
                } else if (side[u] == side[v]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

int main(int argc, char **argv) {
    Dd = argc > 1 ? atoi(argv[1]) : 7;
    DD = argc > 2 ? atoi(argv[2]) : 5;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;
    int target = argc > 5 ? atoi(argv[5]) : 0;

    if (Dd < 2 || Dd > MAXDEG || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 777ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 8; w++) rnd();

    double t0 = now_s();
    deadline = t0 + tl;

    int n_in = 0, m_in = 0, have_start = 0;
    if (scanf("%d %d", &n_in, &m_in) == 2 && n_in > 0 && m_in > 0 && n_in <= MAXN - 2) {
        int ok = 1;
        N = n_in;
        for (int v = 0; v < N; v++) deg_[v] = 0;
        for (int e = 0; e < m_in && ok; e++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) {
                ok = 0;
                break;
            }
            if (u < 0 || v < 0 || u >= N || v >= N || u == v) {
                ok = 0;
                break;
            }
            if (deg_[u] >= Dd || deg_[v] >= Dd) {
                ok = 0;
                break;
            }
            adj[u][deg_[u]++] = v;
            adj[v][deg_[v]++] = u;
        }
        if (ok && color_graph()) have_start = 1;
    }

    if (!have_start) {
        int h = target / 2;
        if (h < Dd) h = Dd;
        if (h > MAXN / 2 - 2) h = MAXN / 2 - 2;
        build_circ(h);
    } else {
        rebuild_lists();
    }

    int have_best = 0;
    int bvN = 0;
    static int bv_adj[MAXN][MAXDEG];
    static int bv_deg[MAXN];
    int chunks = 0;
    int max_chunks = have_start ? 12 : 60;

    while (now_s() < deadline) {
        long long c = bad_count();
        if (c == 0) {
            if (N > bvN) {
                bvN = N;
                save_to(bv_adj, bv_deg);
                have_best = 1;
            }
            if (!grow()) break;
            chunks = 0;
            continue;
        }
        if (chunks >= max_chunks) break;
        chunks++;
        anneal(CHUNK, have_best ? 1.0 : 2.0, 0.05);
    }

    if (!have_best) {
        printf("0 0\n");
        return 0;
    }
    long total = 0;
    for (int v = 0; v < bvN; v++) total += bv_deg[v];
    total /= 2;
    printf("%d %ld\n", bvN, total);
    for (int v = 0; v < bvN; v++) {
        for (int t = 0; t < bv_deg[v]; t++) {
            int u = bv_adj[v][t];
            if (v < u) printf("%d %d\n", v, u);
        }
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions, then bi-Cayley search, then grow-and-repair
# starting from the best valid graph found so far.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(3.0, min(0.9 * time_limit, time_limit - 6.0))
    deadline = t0 + budget
    hard = t0 + max(budget, time_limit - 2.5)

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

    if d >= 3 and D >= 3 and time.monotonic() < deadline - 2.0:
        # Stage 1: bi-Cayley search, seeded with the best known order.
        c1 = 0.5 * (deadline - time.monotonic())
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{c1:.2f}", best_n],
                            timeout=max(2.0, hard - time.monotonic()))
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

        # Stage 2: grow-and-repair. Start from the best valid graph if it is a
        # real construction; otherwise from a random bi-circulant of target order.
        if time.monotonic() < deadline - 2.0:
            c2 = deadline - time.monotonic() - 1.0
            target = max(best_n + 2, int(0.35 * lib.moore_bound(d, D)) // 2 * 2)
            stdin = (best_n, best[1]) if best_n > 2 * d else None
            try:
                out = lib.run_c(REPAIR_SOURCE, [d, D, seed, f"{c2:.2f}", target],
                                stdin_graph=stdin,
                                timeout=max(2.0, hard - time.monotonic()))
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
