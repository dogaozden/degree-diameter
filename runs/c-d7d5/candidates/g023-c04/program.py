import time

import lib


# ----------------------------------------------------------------------------
# Exact baseline: incidence graph of PG(2, q) for the largest prime power
# q with q + 1 <= d (diameter 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Stage 1 engine (parent): bi-Cayley search with breakout local search,
# coordinate polish and near-miss ILS. Vertices A_{i,g} = i*G+g,
# B_{j,h} = (K+j)*G+h, dart (l, i) joins A_{i,g} to B_{P[l][i], g*S[l][i]}.
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
            int k2_pct = 25 + (fails / 20) * 5;
            if (k2_pct > 50) k2_pct = 50;
            K = (rint_(100) < 100 - k2_pct) ? 1 : 2;
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
'''


# ----------------------------------------------------------------------------
# Stage 2 engine (new): annealing over general bipartite graphs with vertex
# growth. No symmetry is imposed. Moves: degree-preserving edge switch,
# moving an edge endpoint onto a deficient vertex, adding an edge between
# deficient vertices, and removing an edge. Cost = ordered pairs at distance
# > D (bitset BFS). Starts from a valid input graph, repeatedly appends a
# new vertex pair and anneals back to cost 0, keeping the largest valid graph.
# ----------------------------------------------------------------------------

SA_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXDG 64
#define MAXCAP 8000
#define STAGE_ITERS 2500

static int Dg = 3, DD = 3;
static int N = 0, CAP = 0, W = 1;
static int *side_ = NULL, *deg = NULL, *adj = NULL;
static int *bkdeg = NULL, *bkadj = NULL;
static int *bestdeg = NULL, *bestadj = NULL;
static int bestN = 0;
static uint64_t *R0 = NULL, *R1 = NULL;
static int *LST[2];
static int NL[2];
static uint64_t rs = 88172645463325252ULL;
static double deadline = 0.0;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }

static double urand(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static long long moore_bound(int d, int D) {
    if (D == 0 || d == 0) return 1;
    if (d == 1) return D >= 1 ? 2 : 1;
    if (d == 2) return 2LL * D;
    long long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (p > (1LL << 40)) p = (1LL << 40);
    }
    return 2 * s;
}

static int has_edge(int u, int v) {
    for (int k = 0; k < deg[u]; k++)
        if (adj[u * Dg + k] == v) return 1;
    return 0;
}

static void add_e(int u, int v) {
    adj[u * Dg + deg[u]++] = v;
    adj[v * Dg + deg[v]++] = u;
}

static void del_e(int u, int v) {
    for (int k = 0; k < deg[u]; k++) {
        if (adj[u * Dg + k] == v) {
            adj[u * Dg + k] = adj[u * Dg + deg[u] - 1];
            deg[u]--;
            break;
        }
    }
    for (int k = 0; k < deg[v]; k++) {
        if (adj[v * Dg + k] == u) {
            adj[v * Dg + k] = adj[v * Dg + deg[v] - 1];
            deg[v]--;
            break;
        }
    }
}

static void rebuild_lists(void) {
    NL[0] = NL[1] = 0;
    for (int v = 0; v < N; v++) LST[side_[v]][NL[side_[v]]++] = v;
}

/* Random vertex of side s with deg < Dg (need_def) or deg > 0 (otherwise). */
static int pick_side(int s, int need_def) {
    int m = NL[s];
    if (m == 0) return -1;
    for (int t = 0; t < 40; t++) {
        int v = LST[s][rint_(m)];
        if (need_def ? (deg[v] < Dg) : (deg[v] > 0)) return v;
    }
    int cnt = 0, pick = -1;
    for (int i = 0; i < m; i++) {
        int v = LST[s][i];
        if (need_def ? (deg[v] < Dg) : (deg[v] > 0)) {
            cnt++;
            if (rint_(cnt) == 0) pick = v;
        }
    }
    return pick;
}

static long long eval_cost(void) {
    int n = N;
    if (n <= 0) return 0;
    memset(R0, 0, sizeof(uint64_t) * (size_t)n * (size_t)W);
    for (int v = 0; v < n; v++) R0[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < DD; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = R1 + (size_t)v * W;
            const uint64_t *src = R0 + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * (size_t)W);
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *su = R0 + (size_t)adj[v * Dg + k] * (size_t)W;
                for (int w = 0; w < W; w++) dst[w] |= su[w];
            }
        }
        uint64_t *t = R0;
        R0 = R1;
        R1 = t;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int cnt = 0;
        const uint64_t *src = R0 + (size_t)v * W;
        for (int w = 0; w < W; w++) cnt += __builtin_popcountll(src[w]);
        bad += n - cnt;
    }
    return bad;
}

static void save_state(int *dd, int *aa) {
    memcpy(dd, deg, sizeof(int) * (size_t)N);
    memcpy(aa, adj, sizeof(int) * (size_t)N * (size_t)Dg);
}

static void load_state(const int *dd, const int *aa) {
    memcpy(deg, dd, sizeof(int) * (size_t)N);
    memcpy(adj, aa, sizeof(int) * (size_t)N * (size_t)Dg);
}

static void save_best(void) {
    save_state(bestdeg, bestadj);
    bestN = N;
}

/* Applies one random move. Returns 1 if the graph changed, 0 otherwise.
   A move only modifies the graph after all checks pass. */
static int do_move(void) {
    int r = rint_(100);
    if (r < 35) {
        int a = pick_side(0, 0), c = pick_side(0, 0);
        if (a < 0 || c < 0 || a == c) return 0;
        int b = adj[a * Dg + rint_(deg[a])];
        int e = adj[c * Dg + rint_(deg[c])];
        if (b == e) return 0;
        if (has_edge(a, e) || has_edge(c, b)) return 0;
        del_e(a, b);
        del_e(c, e);
        add_e(a, e);
        add_e(c, b);
        return 1;
    }
    if (r < 60) {
        int p = pick_side(0, 1);
        if (p < 0) return 0;
        int b = pick_side(1, 0);
        if (b < 0) return 0;
        int a = adj[b * Dg + rint_(deg[b])];
        if (a == p || has_edge(p, b)) return 0;
        del_e(a, b);
        add_e(p, b);
        return 1;
    }
    if (r < 75) {
        int q = pick_side(1, 1);
        if (q < 0) return 0;
        int a = pick_side(0, 0);
        if (a < 0) return 0;
        int b = adj[a * Dg + rint_(deg[a])];
        if (b == q || has_edge(a, q)) return 0;
        del_e(a, b);
        add_e(a, q);
        return 1;
    }
    if (r < 92) {
        int p = pick_side(0, 1), q = pick_side(1, 1);
        if (p < 0 || q < 0) return 0;
        if (has_edge(p, q)) return 0;
        add_e(p, q);
        return 1;
    }
    {
        int a = pick_side(0, 0);
        if (a < 0) return 0;
        int b = adj[a * Dg + rint_(deg[a])];
        del_e(a, b);
        return 1;
    }
}

/* Simulated annealing toward cost 0. Returns the final cost (0 = valid). */
static long long anneal(long long iters, double T0, double T1) {
    long long cur = eval_cost();
    if (cur == 0) return 0;
    for (long long it = 0; it < iters; it++) {
        if ((it & 31) == 0 && now_s() > deadline) break;
        double frac = (double)it / (double)iters;
        double T = T0 * pow(T1 / T0, frac);
        save_state(bkdeg, bkadj);
        if (!do_move()) continue;
        long long c2 = eval_cost();
        long long delta = c2 - cur;
        if (delta <= 0 || urand() < exp(-(double)delta / T)) {
            cur = c2;
            if (cur == 0) return 0;
        } else {
            load_state(bkdeg, bkadj);
        }
    }
    return cur;
}

int main(int argc, char **argv) {
    int d = argc > 1 ? atoi(argv[1]) : 3;
    int D = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;
    if (d < 1 || d > MAXDG || D < 1) {
        printf("0 0\n");
        return 0;
    }
    Dg = d;
    DD = D;
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 987654321ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd();

    int n_in = 0, m_in = 0;
    if (scanf("%d %d", &n_in, &m_in) != 2) {
        n_in = 0;
        m_in = 0;
    }
    if (n_in < 0) n_in = 0;
    if (m_in < 0) m_in = 0;
    int cap_e = m_in + d * d + 4;
    int *eu = malloc(sizeof(int) * (size_t)cap_e);
    int *ev = malloc(sizeof(int) * (size_t)cap_e);
    if (!eu || !ev) {
        printf("0 0\n");
        return 0;
    }
    int mm = 0;
    for (int i = 0; i < m_in; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (mm < cap_e) {
            eu[mm] = u;
            ev[mm] = v;
            mm++;
        }
    }
    if (n_in == 0) {
        /* No start graph: use K_{d,d}. */
        n_in = 2 * d;
        mm = 0;
        for (int i = 0; i < d; i++)
            for (int j = 0; j < d; j++) {
                eu[mm] = i;
                ev[mm] = d + j;
                mm++;
            }
    }

    long long mb = moore_bound(d, D);
    if (mb > MAXCAP) mb = MAXCAP;
    CAP = (int)mb + 4;
    if (CAP < n_in + 4) CAP = n_in + 4;
    W = (CAP + 63) / 64;
    side_ = calloc((size_t)CAP, sizeof(int));
    deg = calloc((size_t)CAP, sizeof(int));
    bkdeg = calloc((size_t)CAP, sizeof(int));
    bestdeg = calloc((size_t)CAP, sizeof(int));
    adj = calloc((size_t)CAP * (size_t)Dg, sizeof(int));
    bkadj = calloc((size_t)CAP * (size_t)Dg, sizeof(int));
    bestadj = calloc((size_t)CAP * (size_t)Dg, sizeof(int));
    R0 = calloc((size_t)CAP * (size_t)W, sizeof(uint64_t));
    R1 = calloc((size_t)CAP * (size_t)W, sizeof(uint64_t));
    LST[0] = malloc(sizeof(int) * (size_t)CAP);
    LST[1] = malloc(sizeof(int) * (size_t)CAP);
    if (!side_ || !deg || !bkdeg || !bestdeg || !adj || !bkadj || !bestadj ||
        !R0 || !R1 || !LST[0] || !LST[1]) {
        printf("0 0\n");
        return 0;
    }

    N = n_in;
    for (int i = 0; i < mm; i++) {
        int u = eu[i], v = ev[i];
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) continue;
        if (deg[u] >= Dg || deg[v] >= Dg) continue;
        if (has_edge(u, v)) continue;
        add_e(u, v);
    }

    /* 2-colour the graph by BFS; a conflict means the input is not bipartite. */
    for (int v = 0; v < N; v++) side_[v] = -1;
    int *q = malloc(sizeof(int) * (size_t)(N + 1));
    int bad_col = 0;
    for (int s = 0; s < N && !bad_col; s++) {
        if (side_[s] >= 0) continue;
        side_[s] = 0;
        int qh = 0, qt = 0;
        q[qt++] = s;
        while (qh < qt && !bad_col) {
            int v = q[qh++];
            for (int k = 0; k < deg[v]; k++) {
                int u = adj[v * Dg + k];
                if (side_[u] < 0) {
                    side_[u] = 1 - side_[v];
                    q[qt++] = u;
                } else if (side_[u] == side_[v]) {
                    bad_col = 1;
                    break;
                }
            }
        }
    }
    free(q);
    if (bad_col) {
        printf("0 0\n");
        return 0;
    }
    rebuild_lists();

    deadline = now_s() + tl;
    int have = 0;
    long long c = anneal(STAGE_ITERS, 30.0, 0.5);
    if (c == 0) {
        save_best();
        have = 1;
    }
    while (now_s() < deadline) {
        if (have) {
            if (bestN + 2 > CAP) break;
            N = bestN;
            load_state(bestdeg, bestadj);
            N = bestN + 2;
            side_[N - 2] = 0;
            side_[N - 1] = 1;
            deg[N - 2] = 0;
            deg[N - 1] = 0;
            rebuild_lists();
        }
        c = anneal(STAGE_ITERS, 30.0, 0.5);
        if (c == 0) {
            save_best();
            have = 1;
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    long long m2 = 0;
    for (int v = 0; v < bestN; v++) m2 += bestdeg[v];
    printf("%d %lld\n", bestN, m2 / 2);
    for (int v = 0; v < bestN; v++) {
        for (int k = 0; k < bestdeg[v]; k++) {
            int u = bestadj[v * Dg + k];
            if (v < u) printf("%d %d\n", v, u);
        }
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue. Target (d=7, D=5): stage 1 runs the parent search, stage 2
# anneals the best graph with vertex growth. Other cases: parent search only.
# Every returned graph is checked, and K_{d,d} is the safe fallback.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    deadline = t_start + max(3.0, min(0.88 * time_limit, time_limit - 5.0))

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

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    use_sa = (d == 7 and D == 5)

    if d >= 3 and D >= 3:
        remaining = deadline - time.monotonic()
        c1 = remaining * 0.5 if use_sa else remaining - 1.5
        if c1 >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{c1:.2f}", best_n],
                                timeout=c1 + 4.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

        if use_sa:
            remaining = deadline - time.monotonic() - 1.0
            if remaining >= 2.0 and best_n >= 2:
                try:
                    out = lib.run_c(SA_SOURCE, [d, D, seed + 101, f"{remaining:.2f}"],
                                    stdin_graph=best, timeout=remaining + 4.0)
                    n, e = lib.parse_graph_text(out)
                    consider(n, e)
                except Exception:
                    pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
