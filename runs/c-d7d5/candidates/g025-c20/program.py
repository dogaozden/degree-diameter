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
# C engine, one source, two modes (argv[6]):
#   mode 0: bi-Cayley breakout search with polish and near-miss ILS (parent engine).
#   mode 1: NEW general (non-group) bipartite simulated annealing. It reads a
#           valid start graph on stdin, repeatedly adds one vertex to each side,
#           and repairs the diameter with edge moves that keep degree <= d.
#           Cost = (unordered pairs at distance > D) + (free degree slots).
#           Reachability is computed with bitsets, so each evaluation is cheap.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
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
            cost_of(c, 1);
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

static int bc_main(int argc, char **argv) {
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
    int fails = 0;
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
            long long span = g0 / 25 + 6 + (long long)(fails / 40) * (g0 / 50 + 1);
            if (span > g0 / 3 + 6) span = g0 / 3 + 6;
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
            fails++;
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

/* ============ mode 1: general bipartite simulated annealing growth ============ */

#define NMAX 4200
#define WMAX 67
#define SMAXD 64
#define EMAX (NMAX * 32)
#define SA_ITERS 8000

static int NA = 0, NB = 0, EE = 0;          /* A = 0..NA-1, B local j -> global NA+j */
static int eA_[EMAX], eB_[EMAX];            /* edge: A global index, B local index */
static int bkA_[EMAX], bkB_[EMAX], bkE_;
static int bestA_[EMAX], bestB_[EMAX], bestE_, bestNA_, bestNB_;
static int vdeg_[NMAX];
static int vnb_[NMAX][SMAXD];
static int defA_[NMAX], defB_[NMAX], nda_, ndb_;
static uint64_t bufX_[NMAX * WMAX], bufY_[NMAX * WMAX];

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static double rf_(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static void rebuild_(void) {
    int n = NA + NB;
    for (int v = 0; v < n; v++) vdeg_[v] = 0;
    for (int e = 0; e < EE; e++) {
        int a = eA_[e], b = NA + eB_[e];
        vnb_[a][vdeg_[a]++] = b;
        vnb_[b][vdeg_[b]++] = a;
    }
}

static int isadj_(int a, int jb) {
    int b = NA + jb;
    for (int k = 0; k < vdeg_[a]; k++)
        if (vnb_[a][k] == b) return 1;
    return 0;
}

/* Number of unordered pairs at distance > DD. */
static long long eval_bad_(void) {
    int n = NA + NB;
    int W = (n + 63) >> 6;
    uint64_t *cur = bufX_, *nxt = bufY_;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * (size_t)W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int s = 0; s < DD; s++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * (size_t)W);
            for (int k = 0; k < vdeg_[v]; k++) {
                const uint64_t *su = cur + (size_t)vnb_[v][k] * W;
                for (int w = 0; w < W; w++) dst[w] |= su[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long long unreached = 0;
    for (int v = 0; v < n; v++) {
        const uint64_t *row = cur + (size_t)v * W;
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(row[w]);
        unreached += n - c;
    }
    return unreached / 2;
}

static long long cost_(long long bad) {
    return bad + ((long long)(NA + NB) * Dd - 2LL * EE);   /* bad pairs + free slots */
}

static void collect_def_(void) {
    nda_ = 0;
    for (int a = 0; a < NA; a++)
        if (vdeg_[a] < Dd) defA_[nda_++] = a;
    ndb_ = 0;
    for (int j = 0; j < NB; j++)
        if (vdeg_[NA + j] < Dd) defB_[ndb_++] = j;
}

static void backup_(void) {
    bkE_ = EE;
    memcpy(bkA_, eA_, sizeof(int) * (size_t)EE);
    memcpy(bkB_, eB_, sizeof(int) * (size_t)EE);
}

static void restore_(void) {
    EE = bkE_;
    memcpy(eA_, bkA_, sizeof(int) * (size_t)EE);
    memcpy(eB_, bkB_, sizeof(int) * (size_t)EE);
    rebuild_();
}

/* Propose one legal local move; returns 0 if none was applied. */
static int propose_(void) {
    int type = rint_(5);
    collect_def_();
    if (type == 0) {                      /* add edge between two free slots */
        if (!nda_ || !ndb_ || EE >= EMAX) return 0;
        int x = defA_[rint_(nda_)], j = defB_[rint_(ndb_)];
        if (isadj_(x, j)) return 0;
        eA_[EE] = x;
        eB_[EE] = j;
        EE++;
        rebuild_();
        return 1;
    }
    if (EE == 0) return 0;
    int e = rint_(EE);
    int a = eA_[e], j = eB_[e];
    if (type == 1) {                      /* insert: (a,j) -> (x,j),(a,y) */
        if (!nda_ || !ndb_ || EE >= EMAX) return 0;
        int x = defA_[rint_(nda_)], y = defB_[rint_(ndb_)];
        if (isadj_(x, j) || isadj_(a, y)) return 0;
        eA_[e] = x;
        eA_[EE] = a;
        eB_[EE] = y;
        EE++;
        rebuild_();
        return 1;
    }
    if (type == 2) {                      /* move an A endpoint to a free A slot */
        if (!nda_) return 0;
        int x = defA_[rint_(nda_)];
        if (x == a || isadj_(x, j)) return 0;
        eA_[e] = x;
        rebuild_();
        return 1;
    }
    if (type == 3) {                      /* move a B endpoint to a free B slot */
        if (!ndb_) return 0;
        int y = defB_[rint_(ndb_)];
        if (y == j || isadj_(a, y)) return 0;
        eB_[e] = y;
        rebuild_();
        return 1;
    }
    /* type 4: switch (a,j),(a2,j2) -> (a,j2),(a2,j) */
    if (EE < 2) return 0;
    int f = rint_(EE);
    if (f == e) return 0;
    int a2 = eA_[f], j2 = eB_[f];
    if (a2 == a || j2 == j) return 0;
    if (isadj_(a, j2) || isadj_(a2, j)) return 0;
    eB_[e] = j2;
    eB_[f] = j;
    rebuild_();
    return 1;
}

/* Simulated annealing on the current state. Returns 1 when bad == 0. */
static int sa_run(long iters) {
    rebuild_();
    long long bad = eval_bad_();
    if (bad == 0) return 1;
    long long cur = cost_(bad);
    for (long it = 0; it < iters; it++) {
        if ((it & 63) == 0 && now_s() > deadline) break;
        double T = 1.2 + (0.15 - 1.2) * ((double)it / (double)iters);
        backup_();
        if (!propose_()) continue;
        long long nb = eval_bad_();
        long long nc = cost_(nb);
        long long delta = nc - cur;
        if (delta <= 0 || rf_() < exp(-(double)delta / T)) {
            cur = nc;
            bad = nb;
            if (bad == 0) return 1;
        } else {
            restore_();
        }
    }
    return bad == 0;
}

static void save_best_(void) {
    bestNA_ = NA;
    bestNB_ = NB;
    bestE_ = EE;
    memcpy(bestA_, eA_, sizeof(int) * (size_t)EE);
    memcpy(bestB_, eB_, sizeof(int) * (size_t)EE);
}

static void load_best_(void) {
    NA = bestNA_;
    NB = bestNB_;
    EE = bestE_;
    memcpy(eA_, bestA_, sizeof(int) * (size_t)EE);
    memcpy(eB_, bestB_, sizeof(int) * (size_t)EE);
}

static int sa_main(int argc, char **argv) {
    Dd = argc > 1 ? atoi(argv[1]) : 3;
    DD = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 777ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 4; w++) rnd();
    deadline = now_s() + tl;
    if (Dd < 1 || Dd > SMAXD || DD < 1) {
        printf("0 0\n");
        return 0;
    }

    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n < 1 || n > NMAX - 8 || m < 0 || m > EMAX - 16) {
        printf("0 0\n");
        return 0;
    }
    int *U = malloc(sizeof(int) * ((size_t)m + 1));
    int *V = malloc(sizeof(int) * ((size_t)m + 1));
    for (int i = 0; i < m; i++) {
        if (scanf("%d %d", &U[i], &V[i]) != 2 || U[i] < 0 || V[i] < 0 ||
            U[i] >= n || V[i] >= n || U[i] == V[i]) {
            printf("0 0\n");
            return 0;
        }
    }
    int *off = calloc((size_t)n + 1, sizeof(int));
    for (int i = 0; i < m; i++) {
        off[U[i] + 1]++;
        off[V[i] + 1]++;
    }
    for (int v = 0; v < n; v++) off[v + 1] += off[v];
    for (int v = 0; v < n; v++)
        if (off[v + 1] - off[v] > Dd) {
            printf("0 0\n");
            return 0;
        }
    int *fillp = malloc(sizeof(int) * ((size_t)n + 1));
    memcpy(fillp, off, sizeof(int) * ((size_t)n + 1));
    int *adj = malloc(sizeof(int) * (2 * (size_t)m + 1));
    for (int i = 0; i < m; i++) {
        adj[fillp[U[i]]++] = V[i];
        adj[fillp[V[i]]++] = U[i];
    }

    /* 2-colour the start graph; colour 0 becomes side A. */
    int *col = malloc(sizeof(int) * (size_t)n);
    int *q = malloc(sizeof(int) * (size_t)n);
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int head = 0, tail = 0;
        q[tail++] = s;
        while (head < tail) {
            int u = q[head++];
            for (int k = off[u]; k < off[u + 1]; k++) {
                int v = adj[k];
                if (col[v] < 0) {
                    col[v] = 1 - col[u];
                    q[tail++] = v;
                } else if (col[v] == col[u]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }
    int na0 = 0;
    for (int v = 0; v < n; v++)
        if (col[v] == 0) na0++;
    int *mp = malloc(sizeof(int) * (size_t)n);
    int ia = 0, ib = 0;
    for (int v = 0; v < n; v++) {
        if (col[v] == 0) mp[v] = ia++;
        else mp[v] = na0 + ib++;
    }
    NA = na0;
    NB = n - na0;
    EE = m;
    for (int i = 0; i < m; i++) {
        int a = U[i], b = V[i];
        if (col[a] != 0) {
            int t = a;
            a = b;
            b = t;
        }
        eA_[i] = mp[a];
        eB_[i] = mp[b] - NA;
    }

    rebuild_();
    int have_valid = (eval_bad_() == 0);
    save_best_();

    while (now_s() < deadline) {
        load_best_();
        if (have_valid) {
            if (NA + NB + 2 > NMAX - 8) break;
            NA++;                          /* grow by one vertex per side */
            NB++;
        }
        if (sa_run(SA_ITERS)) {
            save_best_();
            have_valid = 1;
        }
    }

    int bn = bestNA_ + bestNB_;
    printf("%d %d\n", bn, bestE_);
    for (int e = 0; e < bestE_; e++)
        printf("%d %d\n", bestA_[e], bestNA_ + bestB_[e]);
    return 0;
}

int main(int argc, char **argv) {
    if (argc > 6 && atoi(argv[6]) == 1) return sa_main(argc, argv);
    return bc_main(argc, argv);
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions, then the parent bi-Cayley search, then the
# general annealing growth from the best valid graph. Every stage is validated.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(3.0, min(0.8 * time_limit, time_limit - 8.0))

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
        # Stage 1: bi-Cayley search (mode 0) for a strong start graph.
        s1 = 0.45 * (deadline - time.monotonic())
        if s1 >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{s1:.2f}", best_n, 0],
                                timeout=time_limit - 3.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

        # Stage 2: general bipartite annealing growth (mode 1) from the best valid graph.
        s2 = deadline - time.monotonic() - 1.0
        if s2 >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{s2:.2f}", 0, 1],
                                stdin_graph=best, timeout=time_limit - 3.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
