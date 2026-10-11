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
# C engine 1: bi-Cayley search with breakout local search (clause weighting).
#
# Vertices: A_{i,g} = i*G+g, B_{j,h} = (K+j)*G+h, dart (l, i) joins
# A_{i,g} to B_{P[l][i], g*S[l][i]}. Raw cost = unreached rep-vertex pairs
# within DD steps + PEN * duplicate darts. Cost 0 means a valid graph.
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

/* Returns weighted cost (sum of weights of unreached pairs + PEN * dups).
   Sets g_rawcost = unweighted cost. If bump != 0, the weight of every
   currently unreached pair is increased by one. */
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
            cost_of(c, 1);              /* raise weights of unreached pairs */
            wc = cost_of(c, 0);
            rc = g_rawcost;
            stuck = 0;
        }
    }
    *c = bc;
    return bestraw;
}

/* Best-improvement coordinate sweeps over every single dart value, with
   unit weights (weights must be reset before calling). */
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
    Cfg cur, best_cfg;
    memset(&cur, 0, sizeof(cur));
    memset(&best_cfg, 0, sizeof(best_cfg));

    while (now_s() < deadline) {
        /* Mostly K = 1 (bi-Cayley), sometimes K = 2. */
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
        reset_weights(K, N);
        breakout(&cur, BREAK_ITERS);
        cost_of(&cur, 0);
        if (g_rawcost > 0 && g_rawcost <= POLISH_T) {
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
# C engine 2 (new): pair insertion with annealed repair.
#
# State: a general bipartite graph (side labels 0/1) with max degree Dg and
# diameter bound Dm. Cost = number of unordered vertex pairs at distance > Dm,
# computed exactly with bitset ball expansion (one bitset of n bits per vertex,
# Dm rounds of OR over neighbours).
#
# Loop:
#   * cost 0: save the state, then insert a vertex pair. Pick Dg-1 edges
#     x_i y_i with distinct x's and y's, delete them, add new vertices a (side 0)
#     and b (side 1), edges a-y_i, b-x_i, a-b. Degrees stay <= Dg.
#   * cost > 0: anneal with degree-preserving 2-switches (x y, x2 y2 ->
#     x y2, x2 y, which keeps bipartiteness) and occasional edge additions
#     between deficient vertices. Temperature decays geometrically over STEPS
#     moves; when an attempt runs out, restore the last valid state and insert
#     again with new random choices.
# Output: the last valid graph found.
# ----------------------------------------------------------------------------

C_REPAIR = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 3000
#define MAXW ((MAXN + 63) / 64)
#define MAXDG 64
#define MAXM 100000

static uint64_t rs = 0x2545F4914F6CDD1DULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rint_(int k) { return (int)(rnd() % (uint64_t)k); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int Dg = 3, Dm = 3;
static int n = 0, m = 0;
static int eu[MAXM], ev[MAXM];
static int tu[MAXM], tv[MAXM];
static int side[MAXN], deg[MAXN];
static int nb[MAXN][MAXDG];
static unsigned char adj[MAXN][MAXN];
static uint64_t RA[MAXN][MAXW], RB[MAXN][MAXW];
static int mark_e[MAXM], stampE = 0;
static int usedX[MAXN], usedY[MAXN], stampX = 0, stampY = 0;

static int bn = 0, bm = 0, have_best = 0;
static int beu[MAXM], bev[MAXM], bside[MAXN];

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void set_adj(int u, int v, int val) {
    adj[u][v] = (unsigned char)val;
    adj[v][u] = (unsigned char)val;
}

static void rebuild_adj(void) {
    for (int v = 0; v < n; v++) memset(adj[v], 0, (size_t)n);
    for (int i = 0; i < m; i++) set_adj(eu[i], ev[i], 1);
}

static void build_nb(void) {
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int i = 0; i < m; i++) {
        int u = eu[i], v = ev[i];
        nb[u][deg[u]++] = v;
        nb[v][deg[v]++] = u;
    }
}

/* Number of unordered pairs at distance > Dm (unreachable pairs included). */
static long long bad_pairs(void) {
    int W = (n + 63) / 64;
    build_nb();
    uint64_t (*R)[MAXW] = RA;
    uint64_t (*X)[MAXW] = RB;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) R[v][w] = 0;
        R[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int t = 0; t < Dm; t++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) X[v][w] = R[v][w];
            for (int k = 0; k < deg[v]; k++) {
                int u = nb[v][k];
                for (int w = 0; w < W; w++) X[v][w] |= R[u][w];
            }
        }
        uint64_t (*tmp)[MAXW] = R;
        R = X;
        X = tmp;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(R[v][w]);
        bad += n - c;
    }
    return bad / 2;
}

static int two_colour(void) {
    static int stk[MAXN];
    build_nb();
    for (int v = 0; v < n; v++) side[v] = -1;
    for (int s = 0; s < n; s++) {
        if (side[s] != -1) continue;
        side[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp > 0) {
            int u = stk[--sp];
            for (int k = 0; k < deg[u]; k++) {
                int v = nb[u][k];
                if (side[v] == -1) {
                    side[v] = 1 - side[u];
                    stk[sp++] = v;
                } else if (side[v] == side[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

/* Add a vertex pair by edge cutting. Returns 0 if no valid cut was found. */
static int insert_pair(void) {
    int k = Dg - 1;
    if (k < 1 || m < k || n + 2 > MAXN) return 0;
    build_nb();
    stampE++;
    stampX++;
    stampY++;
    int px[MAXDG], py[MAXDG], np = 0;
    for (int tr = 0; tr < 64 * k && np < k; tr++) {
        int i = rint_(m);
        if (mark_e[i] == stampE) continue;
        int x = eu[i], y = ev[i];
        if (side[x] != 0) {
            int t = x;
            x = y;
            y = t;
        }
        if (usedX[x] == stampX || usedY[y] == stampY) continue;
        mark_e[i] = stampE;
        usedX[x] = stampX;
        usedY[y] = stampY;
        px[np] = x;
        py[np] = y;
        np++;
    }
    if (np < k) return 0;
    int a = n, b = n + 1;
    int nm = 0;
    for (int i = 0; i < m; i++) {
        if (mark_e[i] != stampE) {
            tu[nm] = eu[i];
            tv[nm] = ev[i];
            nm++;
        }
    }
    for (int j = 0; j < np; j++) {
        tu[nm] = px[j];
        tv[nm] = b;
        nm++;
        tu[nm] = a;
        tv[nm] = py[j];
        nm++;
    }
    tu[nm] = a;
    tv[nm] = b;
    nm++;
    memcpy(eu, tu, sizeof(int) * (size_t)nm);
    memcpy(ev, tv, sizeof(int) * (size_t)nm);
    m = nm;
    side[a] = 0;
    side[b] = 1;
    n += 2;
    rebuild_adj();
    return 1;
}

static void save_best(void) {
    bn = n;
    bm = m;
    have_best = 1;
    memcpy(beu, eu, sizeof(int) * (size_t)m);
    memcpy(bev, ev, sizeof(int) * (size_t)m);
    memcpy(bside, side, sizeof(int) * (size_t)n);
}

static void load_best(void) {
    n = bn;
    m = bm;
    memcpy(eu, beu, sizeof(int) * (size_t)m);
    memcpy(ev, bev, sizeof(int) * (size_t)m);
    memcpy(side, bside, sizeof(int) * (size_t)n);
    rebuild_adj();
}

int main(int argc, char **argv) {
    Dg = argc > 1 ? atoi(argv[1]) : 3;
    Dm = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;
    long STEPS = argc > 5 ? atol(argv[5]) : 6000;
    if (Dg < 1 || Dg >= MAXDG || Dm < 1 || STEPS < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 99991ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 4; w++) rnd();
    double deadline = now_s() + tl;

    if (scanf("%d %d", &n, &m) != 2 || n < 1 || n > MAXN - 2 || m < 0 ||
        m > n * Dg / 2 || m > MAXM - 2) {
        printf("0 0\n");
        return 0;
    }
    for (int i = 0; i < m; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) {
            printf("0 0\n");
            return 0;
        }
        if (eu[i] < 0 || eu[i] >= n || ev[i] < 0 || ev[i] >= n || eu[i] == ev[i]) {
            printf("0 0\n");
            return 0;
        }
    }
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int i = 0; i < m; i++) {
        deg[eu[i]]++;
        deg[ev[i]]++;
    }
    for (int v = 0; v < n; v++) {
        if (deg[v] > Dg) {
            printf("0 0\n");
            return 0;
        }
    }
    for (int v = 0; v < n; v++) memset(adj[v], 0, (size_t)n);
    for (int i = 0; i < m; i++) {
        if (adj[eu[i]][ev[i]]) {
            printf("0 0\n");
            return 0;
        }
        set_adj(eu[i], ev[i], 1);
    }
    if (!two_colour()) {
        printf("0 0\n");
        return 0;
    }

    long long cur = bad_pairs();
    long s_since = 0;
    double T0 = 1.0, Tmin = 0.05;

    while (now_s() < deadline) {
        if (cur == 0) {
            save_best();
            if (!insert_pair()) break;
            cur = bad_pairs();
            s_since = 0;
            continue;
        }
        if (s_since >= STEPS) {
            s_since = 0;
            if (have_best) {
                load_best();
                cur = bad_pairs();
            }
            continue;
        }
        double frac = (double)s_since / (double)STEPS;
        double T = T0 * pow(Tmin / T0, frac);
        s_since++;
        build_nb();

        if (rint_(10) == 0) {
            /* Edge addition between two deficient vertices on opposite sides. */
            int x = -1, y = -1;
            for (int tr = 0; tr < 100; tr++) {
                int a = rint_(n), b = rint_(n);
                if (side[a] == side[b]) continue;
                if (side[a] == 1) {
                    int t = a;
                    a = b;
                    b = t;
                }
                if (deg[a] >= Dg || deg[b] >= Dg || adj[a][b]) continue;
                x = a;
                y = b;
                break;
            }
            if (x < 0 || m >= MAXM) continue;
            eu[m] = x;
            ev[m] = y;
            m++;
            set_adj(x, y, 1);
            long long c2 = bad_pairs();
            if (c2 <= cur || rdbl() < exp(-(double)(c2 - cur) / T)) {
                cur = c2;
            } else {
                m--;
                set_adj(x, y, 0);
            }
        } else {
            /* Degree-preserving 2-switch keeping the bipartition. */
            if (m < 2) continue;
            int i = rint_(m), j = rint_(m);
            if (i == j) continue;
            int x = eu[i], y = ev[i];
            if (side[x] != 0) {
                int t = x;
                x = y;
                y = t;
            }
            int x2 = eu[j], y2 = ev[j];
            if (side[x2] != 0) {
                int t = x2;
                x2 = y2;
                y2 = t;
            }
            if (x == x2 || y == y2 || adj[x][y2] || adj[x2][y]) continue;
            set_adj(x, y, 0);
            set_adj(x2, y2, 0);
            set_adj(x, y2, 1);
            set_adj(x2, y, 1);
            eu[i] = x;
            ev[i] = y2;
            eu[j] = x2;
            ev[j] = y;
            long long c2 = bad_pairs();
            if (c2 <= cur || rdbl() < exp(-(double)(c2 - cur) / T)) {
                cur = c2;
            } else {
                set_adj(x, y2, 0);
                set_adj(x2, y, 0);
                set_adj(x, y, 1);
                set_adj(x2, y2, 1);
                eu[i] = x;
                ev[i] = y;
                eu[j] = x2;
                ev[j] = y2;
            }
        }
    }
    if (cur == 0) save_best();
    if (!have_best) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", bn, bm);
    for (int i = 0; i < bm; i++) printf("%d %d\n", beu[i], bev[i]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions, then bi-Cayley search, then annealed
# pair insertion (C_REPAIR) on the best graph found so far.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(3.0, min(0.9 * time_limit, time_limit - 4.0))

    def left():
        return deadline - time.monotonic()

    def elapsed_margin():
        return time_limit - (time.monotonic() - start) - 3.0

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

    if D >= 4 and left() > 0:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Stage 1: bi-Cayley breakout search, seeded with the best known order.
    if d >= 3 and D >= 3 and left() > 4.0:
        b1 = 0.5 * left() - 1.0
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{b1:.2f}", best_n],
                            timeout=max(1.0, min(b1 + 6.0, elapsed_margin())))
            consider(*lib.parse_graph_text(out))
        except Exception:
            pass

    # Stage 2: pair insertion with annealed repair on the best graph so far.
    if d >= 2 and D >= 2 and left() > 2.0:
        b2 = left() - 1.0
        try:
            out = lib.run_c(C_REPAIR, [d, D, seed, f"{b2:.2f}", 6000],
                            stdin_graph=best,
                            timeout=max(1.0, min(b2 + 6.0, elapsed_margin())))
            consider(*lib.parse_graph_text(out))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
