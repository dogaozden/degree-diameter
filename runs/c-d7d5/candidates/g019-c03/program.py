import itertools
import math
import random
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
# Stage 2 C engine (previous parent search, kept as a fallback): bi-Cayley
# breakout local search with clause weighting and a coordinate polish.
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
# Stage 1 C engine (new): simulated annealing over bi-Cayley voltages on an
# explicit list of groups Z_m x|_r Z_k. Vertices A_g = g, B_h = G + h, and
# dart l joins A_g to B_{g*s_l}. Left multiplication is an automorphism, so
# validity only needs BFS from A_e and B_e. Cost = unreached vertices from A_e
# plus unreached B-vertices from B_e. Groups are passed as argv triples, and
# the search climbs in group order inside a sliding window above the best
# order found so far.
# ----------------------------------------------------------------------------

SA_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXDEG 16
#define MAXORD 2000
#define MAXG 8192
#define WIN 6

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

static int dg = 3, DD = 3;
static int GM = 1, GK = 1, GO = 1;
static int gpow[MAXORD];
static int *MUL = NULL, *INV = NULL;
static int *VIS = NULL, *QU = NULL;
static int STAMP = 0, CAP2 = 0;
static int SV[MAXDEG], BSV[MAXDEG];

static int gmul(int x, int y) {
    int a = x / GK, b = x % GK;
    int c = y / GK, d = y % GK;
    int t = (a + gpow[b] * c) % GM;
    return t * GK + (b + d) % GK;
}

static int build_group(int m, int k, int r) {
    if (m < 1 || k < 1 || m * k > MAXORD) return 0;
    GM = m;
    GK = k;
    GO = m * k;
    long long p = 1 % m;
    for (int b = 0; b < k; b++) {
        gpow[b] = (int)p;
        p = (p * (long long)r) % m;
    }
    free(MUL);
    free(INV);
    MUL = malloc(sizeof(int) * (size_t)GO * (size_t)GO);
    INV = malloc(sizeof(int) * (size_t)GO);
    if (!MUL || !INV) return 0;
    for (int x = 0; x < GO; x++)
        for (int y = 0; y < GO; y++)
            MUL[x * GO + y] = gmul(x, y);
    for (int x = 0; x < GO; x++) {
        INV[x] = -1;
        for (int y = 0; y < GO; y++) {
            if (MUL[x * GO + y] == 0) {
                INV[x] = y;
                break;
            }
        }
        if (INV[x] < 0) return 0;
    }
    if (2 * GO > CAP2) {
        free(VIS);
        free(QU);
        CAP2 = 2 * GO;
        VIS = calloc((size_t)CAP2, sizeof(int));
        QU = malloc(sizeof(int) * (size_t)CAP2);
        if (!VIS || !QU) return 0;
        STAMP = 0;
    }
    return 1;
}

static int bfs_reach(int src, int *cntB) {
    STAMP++;
    if (STAMP > 1000000000) {
        memset(VIS, 0, sizeof(int) * (size_t)CAP2);
        STAMP = 1;
    }
    int head = 0, tail = 0;
    VIS[src] = STAMP;
    QU[tail++] = src;
    for (int lvl = 0; lvl < DD; lvl++) {
        int end = tail;
        if (head == end) break;
        while (head < end) {
            int u = QU[head++];
            if (u < GO) {
                const int *row = MUL + (size_t)u * (size_t)GO;
                for (int l = 0; l < dg; l++) {
                    int v = GO + row[SV[l]];
                    if (VIS[v] != STAMP) {
                        VIS[v] = STAMP;
                        QU[tail++] = v;
                    }
                }
            } else {
                int h = u - GO;
                const int *row = MUL + (size_t)h * (size_t)GO;
                for (int l = 0; l < dg; l++) {
                    int v = row[INV[SV[l]]];
                    if (VIS[v] != STAMP) {
                        VIS[v] = STAMP;
                        QU[tail++] = v;
                    }
                }
            }
        }
    }
    int cb = 0;
    for (int i = 0; i < tail; i++)
        if (QU[i] >= GO) cb++;
    *cntB = cb;
    return tail;
}

static int cost_now(void) {
    int cb1 = 0, cb2 = 0;
    int r1 = bfs_reach(0, &cb1);
    bfs_reach(GO, &cb2);
    return (2 * GO - r1) + (GO - cb2);
}

static int in_S(int x, int upto) {
    for (int i = 0; i < upto; i++)
        if (SV[i] == x) return 1;
    return 0;
}

/* Annealing from a random start. Leaves the best voltages in BSV.
   Returns 1 if a cost-0 (valid) assignment was found. */
static int anneal(double until) {
    for (int l = 0; l < dg; l++) {
        int x;
        do {
            x = rint_(GO);
        } while (in_S(x, l));
        SV[l] = x;
    }
    int cur = cost_now();
    int best = cur;
    memcpy(BSV, SV, sizeof(int) * (size_t)dg);
    const double T0 = 2.0, T1 = 0.12;
    const long CYC = 30000;
    long it = 0;
    while (best > 0) {
        if ((it & 255) == 0 && now_s() > until) break;
        long ph = it % CYC;
        double T = T0 * pow(T1 / T0, (double)ph / (double)CYC);
        it++;
        int l = rint_(dg);
        int x = rint_(GO);
        if (in_S(x, dg)) continue;
        int old = SV[l];
        SV[l] = x;
        int c2 = cost_now();
        int delta = c2 - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = c2;
            if (cur < best) {
                best = cur;
                memcpy(BSV, SV, sizeof(int) * (size_t)dg);
            }
        } else {
            SV[l] = old;
        }
    }
    return best == 0;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        printf("0 0\n");
        return 0;
    }
    dg = atoi(argv[1]);
    DD = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    double att = atof(argv[5]);
    if (dg < 1 || dg > MAXDEG || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    int ng = (argc - 6) / 3;
    if (ng > MAXG) ng = MAXG;
    static int gm[MAXG], gk[MAXG], gr[MAXG];
    int minG = 1 << 30;
    int nvalid = 0;
    for (int i = 0; i < ng; i++) {
        gm[i] = atoi(argv[6 + 3 * i]);
        gk[i] = atoi(argv[7 + 3 * i]);
        gr[i] = atoi(argv[8 + 3 * i]);
        int Gc = gm[i] * gk[i];
        if (gm[i] < 1 || gk[i] < 1 || Gc < dg || Gc > MAXORD) {
            gm[i] = 0;
            continue;
        }
        if (Gc < minG) minG = Gc;
        nvalid++;
    }
    if (nvalid == 0) {
        printf("0 0\n");
        return 0;
    }

    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 4; w++) rnd();

    double deadline = now_s() + tl;
    int bestG = 0, bm = 1, bk = 1, br = 1;
    int have = 0;
    int SOL[MAXDEG];

    while (now_s() < deadline) {
        int attempted = 0;
        for (int i = 0; i < ng; i++) {
            if (now_s() >= deadline) break;
            if (gm[i] == 0) continue;
            int Gc = gm[i] * gk[i];
            int base = bestG > 0 ? bestG : minG - 1;
            if (Gc <= base || Gc > base + WIN) continue;
            if (!build_group(gm[i], gk[i], gr[i])) continue;
            attempted++;
            double until = now_s() + att;
            if (until > deadline) until = deadline;
            if (anneal(until)) {
                bestG = GO;
                bm = gm[i];
                bk = gk[i];
                br = gr[i];
                memcpy(SOL, BSV, sizeof(int) * (size_t)dg);
                have = 1;
            }
        }
        if (!attempted) break;
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    if (!build_group(bm, bk, br)) {
        printf("0 0\n");
        return 0;
    }
    int n = 2 * GO;
    long m = (long)dg * GO;
    printf("%d %ld\n", n, m);
    for (int g = 0; g < GO; g++) {
        for (int l = 0; l < dg; l++) {
            int h = MUL[g * GO + SOL[l]];
            printf("%d %d\n", g, GO + h);
        }
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue.
# ----------------------------------------------------------------------------

def _group_triples(d, glo, ghi, seed, per_order=3):
    """Candidate groups Z_m x|_r Z_k with m*k = G for each G in [glo, ghi].

    Each order gets the cyclic group first, then a few random others
    (direct products and semidirect products with r^k = 1 mod m).
    """
    rng = random.Random(seed * 1000003 + 991)
    out = []
    for G in range(glo, ghi + 1):
        if G < d:
            continue
        cands = [(G, 1, 1)]
        for k in range(2, G // 2 + 1):
            if G % k:
                continue
            m = G // k
            cands.append((m, k, 1))
            for _ in range(60):
                r = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                    cands.append((m, k, r))
                    break
        uniq = []
        for c in cands:
            if c not in uniq:
                uniq.append(c)
        first, rest = uniq[0], uniq[1:]
        rng.shuffle(rest)
        out.extend([first] + rest[: per_order - 1])
    return out


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

    # Stage 1 (new): annealing over explicit semidirect-product groups.
    if d >= 3 and D >= 3:
        rem = deadline - time.monotonic()
        if rem > 8.0:
            moore = lib.moore_bound(d, D)
            glo = max(d, best_n // 2 + 1, int(0.25 * moore / 2))
            ghi = min(1900, max(glo + 12, int(0.46 * moore / 2)))
            triples = _group_triples(d, glo, ghi, seed)
            flat = [str(x) for t in triples for x in t]
            sa_budget = max(2.0, 0.6 * rem - 1.0)
            att = min(1.5, max(0.25, sa_budget / 40.0))
            try:
                out = lib.run_c(SA_SOURCE,
                                [d, D, seed, f"{sa_budget:.2f}", f"{att:.2f}", *flat],
                                timeout=sa_budget + 8.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    # Stage 2: the previous breakout engine, seeded with the best order so far.
    rem = deadline - time.monotonic() - 1.5
    if d >= 3 and D >= 3 and rem >= 2.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{rem:.2f}", best_n],
                            timeout=time_limit - 3.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
