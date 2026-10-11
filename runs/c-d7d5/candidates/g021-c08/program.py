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
# search: when no valid graph is found, the best near-miss is kept and
# re-attacked with a small random perturbation.
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

/* Returns weighted cost (sum of weights of unreached pairs + PEN * dups).
   Sets g_rawcost to the unweighted cost. If bump != 0, the weight of every
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
    Cfg cur, best_cfg, near;
    memset(&cur, 0, sizeof(cur));
    memset(&best_cfg, 0, sizeof(best_cfg));
    memset(&near, 0, sizeof(near));

    /* Best near-miss (smallest raw cost, still above best_n) kept for ILS. */
    int have_near = 0;
    int nM = 1, nK = 1, nR = 1;
    long long nraw = 0;

    while (now_s() < deadline) {
        int K, M, Kk, R;
        int from_near = have_near && (rint_(100) < NEAR_PCT);
        if (from_near) {
            /* Perturb the stored near-miss in its own group. */
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
            /* Mostly K = 1 (bi-Cayley), sometimes K = 2. */
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
        /* Polish threshold scales with the order so larger near-miss
           graphs also get the exhaustive coordinate sweep. */
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
# C engine 2 (different family): unstructured grow-and-repair annealing.
# Input: a bipartite graph whose first half is side A and second half side B,
# with spare degree allowed. Moves: add an edge between deficient vertices,
# transfer an edge endpoint to a deficient vertex, or a 2-switch. The cost is
# the number of unordered vertex pairs at distance > DIAM (bitset BFS on the
# edge list). Prints a valid graph of the same order when cost 0 is reached,
# else "0 0".
# ----------------------------------------------------------------------------

SA_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

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

static int pop64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int N, H, DEG, DIAM, W, M;
static int *EA, *EB, *deg, *defA, *defB, *BA, *BB;
static unsigned char *adj;
static uint64_t *R, *R2;
static long long best;
static int bestM;

#define AD(a, b) adj[(size_t)(a) * (size_t)N + (size_t)(b)]

static void setadj(int a, int b, unsigned char v) {
    AD(a, b) = v;
    AD(b, a) = v;
}

static long long cost_eval(void) {
    size_t tot = (size_t)N * (size_t)W;
    for (int v = 0; v < N; v++) {
        uint64_t *rv = R + (size_t)v * (size_t)W;
        memset(rv, 0, sizeof(uint64_t) * (size_t)W);
        rv[v >> 6] |= 1ULL << (v & 63);
    }
    for (int lvl = 0; lvl < DIAM; lvl++) {
        memcpy(R2, R, sizeof(uint64_t) * tot);
        for (int e = 0; e < M; e++) {
            uint64_t *ra = R + (size_t)EA[e] * (size_t)W;
            uint64_t *rb = R + (size_t)EB[e] * (size_t)W;
            uint64_t *na = R2 + (size_t)EA[e] * (size_t)W;
            uint64_t *nb = R2 + (size_t)EB[e] * (size_t)W;
            for (int w = 0; w < W; w++) {
                na[w] |= rb[w];
                nb[w] |= ra[w];
            }
        }
        uint64_t *t = R;
        R = R2;
        R2 = t;
    }
    long long bad = 0;
    for (int v = 0; v < N; v++) {
        const uint64_t *rv = R + (size_t)v * (size_t)W;
        int c = 0;
        for (int w = 0; w < W; w++) c += pop64(rv[w]);
        bad += N - c;
    }
    return bad / 2;
}

static void save_best(long long cur) {
    if (cur < best) {
        best = cur;
        bestM = M;
        memcpy(BA, EA, sizeof(int) * (size_t)M);
        memcpy(BB, EB, sizeof(int) * (size_t)M);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 777ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 4; i++) rnd();

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2 || n < 2 || (n & 1) || n > 6000 || m < 0 || DEG < 1 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    H = n / 2;
    W = (N + 63) / 64;
    int cap = N * DEG + 4;
    EA = malloc(sizeof(int) * (size_t)cap);
    EB = malloc(sizeof(int) * (size_t)cap);
    BA = malloc(sizeof(int) * (size_t)cap);
    BB = malloc(sizeof(int) * (size_t)cap);
    deg = calloc((size_t)N, sizeof(int));
    defA = malloc(sizeof(int) * (size_t)N);
    defB = malloc(sizeof(int) * (size_t)N);
    adj = calloc((size_t)N * (size_t)N, 1);
    R = malloc(sizeof(uint64_t) * (size_t)N * (size_t)W);
    R2 = malloc(sizeof(uint64_t) * (size_t)N * (size_t)W);
    if (!EA || !EB || !BA || !BB || !deg || !defA || !defB || !adj || !R || !R2) {
        printf("0 0\n");
        return 0;
    }

    M = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) {
            printf("0 0\n");
            return 0;
        }
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) {
            printf("0 0\n");
            return 0;
        }
        int a, b;
        if (u < H && v >= H) {
            a = u;
            b = v;
        } else if (v < H && u >= H) {
            a = v;
            b = u;
        } else {
            printf("0 0\n");
            return 0;
        }
        if (AD(a, b) || deg[a] >= DEG || deg[b] >= DEG || M >= cap) {
            printf("0 0\n");
            return 0;
        }
        setadj(a, b, 1);
        EA[M] = a;
        EB[M] = b;
        M++;
        deg[a]++;
        deg[b]++;
    }

    long long cur = cost_eval();
    best = cur;
    bestM = M;
    memcpy(BA, EA, sizeof(int) * (size_t)M);
    memcpy(BB, EB, sizeof(int) * (size_t)M);

    double t0 = now_s();
    double deadline = t0 + tl;
    const double T0 = 1.5, T1 = 0.05;
    double T = T0;
    long long it = 0;

    while (best > 0) {
        save_best(cur);
        if (best == 0) break;
        if ((it & 31) == 0) {
            double now = now_s();
            if (now >= deadline) break;
            double frac = (now - t0) / tl;
            if (frac > 1.0) frac = 1.0;
            T = T0 * pow(T1 / T0, frac);
        }
        it++;

        int nA = 0, nB = 0;
        for (int v = 0; v < H; v++)
            if (deg[v] < DEG) defA[nA++] = v;
        for (int v = H; v < N; v++)
            if (deg[v] < DEG) defB[nB++] = v;

        int mv = rint_(100);
        if (mv < 25) {
            /* add an edge between two deficient vertices (never raises cost) */
            if (nA == 0 || nB == 0 || M >= cap) continue;
            int a = defA[rint_(nA)];
            int b = defB[rint_(nB)];
            if (AD(a, b)) continue;
            EA[M] = a;
            EB[M] = b;
            M++;
            deg[a]++;
            deg[b]++;
            setadj(a, b, 1);
            cur = cost_eval();
        } else if (mv < 55) {
            /* move one endpoint of a random edge onto a deficient vertex */
            if (M == 0 || (nA == 0 && nB == 0)) continue;
            int i = rint_(M);
            int a1 = EA[i], b1 = EB[i];
            int useB = (nB > 0) && (nA == 0 || rint_(2));
            if (useB) {
                int x = defB[rint_(nB)];
                if (x == b1 || AD(a1, x)) continue;
                setadj(a1, b1, 0);
                setadj(a1, x, 1);
                EB[i] = x;
                deg[b1]--;
                deg[x]++;
                long long nc = cost_eval();
                if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                    cur = nc;
                } else {
                    EB[i] = b1;
                    deg[x]--;
                    deg[b1]++;
                    setadj(a1, x, 0);
                    setadj(a1, b1, 1);
                    cur = cost_eval();
                }
            } else {
                int y = defA[rint_(nA)];
                if (y == a1 || AD(y, b1)) continue;
                setadj(a1, b1, 0);
                setadj(y, b1, 1);
                EA[i] = y;
                deg[a1]--;
                deg[y]++;
                long long nc = cost_eval();
                if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                    cur = nc;
                } else {
                    EA[i] = a1;
                    deg[y]--;
                    deg[a1]++;
                    setadj(y, b1, 0);
                    setadj(a1, b1, 1);
                    cur = cost_eval();
                }
            }
        } else {
            /* 2-switch: keeps every degree and the bipartition */
            if (M < 2) continue;
            int i = rint_(M), j = rint_(M);
            if (i == j) continue;
            int a1 = EA[i], b1 = EB[i], a2 = EA[j], b2 = EB[j];
            if (a1 == a2 || b1 == b2) continue;
            if (AD(a1, b2) || AD(a2, b1)) continue;
            setadj(a1, b1, 0);
            setadj(a2, b2, 0);
            setadj(a1, b2, 1);
            setadj(a2, b1, 1);
            EB[i] = b2;
            EB[j] = b1;
            long long nc = cost_eval();
            if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
            } else {
                EB[i] = b1;
                EB[j] = b2;
                setadj(a1, b2, 0);
                setadj(a2, b1, 0);
                setadj(a1, b1, 1);
                setadj(a2, b2, 1);
                cur = cost_eval();
            }
        }
    }

    save_best(cur);
    if (best != 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", N, bestM);
    for (int e = 0; e < bestM; e++) printf("%d %d\n", BA[e], BB[e]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions, then the bi-Cayley search, then growth by
# annealing repair of the best graph found so far.
# ----------------------------------------------------------------------------

def _grow_graph(graph, d, D, seed, budget):
    """Insert one vertex pair (new A and B vertex) and let the SA engine repair it.

    Returns a strictly larger valid graph, or None.
    """
    n, edges = graph
    h0 = n // 2
    h = h0 + 1

    def mp(v):
        # A labels 0..h0-1 stay; B labels h0..n-1 shift by one so B is h..2h-1.
        return v if v < h0 else v + 1

    ed = [(mp(u), mp(v)) for u, v in edges]
    try:
        out = lib.run_c(SA_SOURCE, [d, D, seed, f"{budget:.2f}"],
                        stdin_graph=(2 * h, ed), timeout=budget + 3.0)
        n2, e2 = lib.parse_graph_text(out)
    except Exception:
        return None
    if n2 > n and lib.is_valid(n2, e2, d, D):
        return n2, e2
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

    # Stage 1: bi-Cayley breakout search in C (about half the remaining time).
    if d >= 3 and D >= 3:
        c_budget = 0.55 * (deadline - time.monotonic()) - 1.0
        if c_budget >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{c_budget:.2f}", best_n],
                                timeout=c_budget + 3.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    # Stage 2: unstructured grow-and-repair annealing, one vertex pair at a time.
    if d >= 3 and D >= 3:
        step = 0
        while best_n < lib.moore_bound(d, D):
            budget = deadline - time.monotonic() - 1.0
            if budget < 2.0:
                break
            cand = _grow_graph(best, d, D, seed * 1000 + step + 7, budget)
            step += 1
            if cand is None:
                break
            best = cand
            best_n = cand[0]

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
