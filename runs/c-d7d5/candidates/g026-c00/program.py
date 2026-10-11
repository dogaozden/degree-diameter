import time

import lib


# ----------------------------------------------------------------------------
# Exact baseline: incidence graph of PG(2, q), q the largest prime power with
# q + 1 <= d. It has diameter 3, so it is valid for every D >= 3.
# ----------------------------------------------------------------------------

def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# C engine: simulated annealing over bi-Cayley lifts with NON-ABELIAN groups.
#
# Each lift has K base vertices per side. Group G = Z_m x|_r Z_k (r^k = 1 mod m),
# element (a, b) coded as a*k+b. Vertices: A_{i,g} = i*G+g, B_{j,h} = (K+j)*G+h.
# Dart (l, i) joins A_{i,g} to B_{P[l][i], g*S[l][i]}. Left multiplication by the
# group is an automorphism, so BFS from the 2K orbit representatives suffices.
#
# Cost = unreached (representative, vertex) pairs within DD steps + PEN * duplicate
# darts. Cost 0 means a valid graph of order 2*K*G. Moves are random S changes and
# swaps of P entries; acceptance follows a cooling schedule. Groups are visited in
# sessions. Each session targets an order slightly above the best found so far.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 64
#define MAXK 4
#define MAXN 8192
#define PEN 40
#define RUN_STEPS 40000
#define SESSION_S 7.0
#define T0 3.0
#define T1 0.25
#define PERT 4

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
static long long gpow[64];
static double deadline = 0.0;

static void set_group(int m, int k, int r) {
    GM = m;
    GK = k;
    GG = m * k;
    long long p = 1 % m;
    for (int b = 0; b < k; b++) {
        gpow[b] = p;
        p = (p * r) % m;
    }
}

static int gmul(int x, int y) {
    int a = x / GK, b = x % GK;
    int c = y / GK, d = y % GK;
    long long t = ((long long)a + gpow[b] * (long long)c) % GM;
    return (int)t * GK + (b + d) % GK;
}

static int g_adj[MAXN * MAXD];
static int g_cnt[MAXN];
static int g_vis[MAXN];
static int g_q[MAXN];
static int g_stamp = 0;

static void build_adj(const Cfg *c) {
    int K = c->K, G = c->G, N = 2 * K * G;
    for (int v = 0; v < N; v++) g_cnt[v] = 0;
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
}

static long long cost_eval(const Cfg *c) {
    int K = c->K, G = c->G, N = 2 * K * G;
    build_adj(c);
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < Dd; l1++)
            for (int l2 = l1 + 1; l2 < Dd; l2++)
                if (c->P[l1][i] == c->P[l2][i] && c->S[l1][i] == c->S[l2][i])
                    dup++;
    long long raw = 0;
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
        raw += (long long)(N - tail);
    }
    return raw + (long long)PEN * dup;
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
    c->G = GG;
}

static void perturb(Cfg *c, int np) {
    for (int t = 0; t < np; t++) {
        int l = rint_(Dd);
        int i = rint_(c->K);
        c->S[l][i] = rint_(GG);
    }
}

/* Simulated annealing. Returns the best cost seen; *best holds that state. */
static long long anneal(Cfg *c, long steps, Cfg *best) {
    long long cur = cost_eval(c);
    long long bestc = cur;
    *best = *c;
    if (cur == 0) return 0;
    double lr = log(T1 / T0);
    for (long t = 0; t < steps; t++) {
        if ((t & 255) == 0 && now_s() > deadline) break;
        double T = T0 * exp(lr * (double)t / (double)steps);
        int l = rint_(Dd);
        int i = rint_(c->K);
        int kind = (c->K >= 2 && rint_(3) == 0);
        int i2 = 0, olds = 0;
        if (kind) {
            i2 = rint_(c->K - 1);
            if (i2 >= i) i2++;
            int tmp = c->P[l][i];
            c->P[l][i] = c->P[l][i2];
            c->P[l][i2] = tmp;
        } else {
            olds = c->S[l][i];
            c->S[l][i] = rint_(GG);
        }
        long long nc = cost_eval(c);
        long long delta = nc - cur;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cur = nc;
            if (cur < bestc) {
                bestc = cur;
                *best = *c;
                if (cur == 0) return 0;
            }
        } else {
            if (kind) {
                int tmp = c->P[l][i];
                c->P[l][i] = c->P[l][i2];
                c->P[l][i2] = tmp;
            } else {
                c->S[l][i] = olds;
            }
        }
    }
    return bestc;
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

static const int KF[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 24};

static void sample_group(long long target, int *oM, int *oK, int *oR) {
    int nk = (int)(sizeof(KF) / sizeof(KF[0]));
    int k = KF[rint_(nk)];
    long long m = (target + k - 1) / k;
    if (m < 2) m = 2;
    int r = 1;
    if (k > 1 && m > 2) {
        for (int t = 0; t < 300; t++) {
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
    long long min_n = argc > 5 ? atoll(argv[5]) : 0;
    long long start_n = argc > 6 ? atoll(argv[6]) : 0;

    if (Dd < 1 || Dd > MAXD || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 8; w++) rnd();

    double t0 = now_s();
    deadline = t0 + tl;

    long long best_n = min_n;
    long long tgt = start_n > best_n + 2 ? start_n : best_n + 2;
    if (tgt > MAXN / 2) tgt = MAXN / 2;
    int have = 0;
    Cfg best_out;
    memset(&best_out, 0, sizeof best_out);
    int bM = 1, bK = 1, bR = 1;

    while (now_s() < deadline) {
        int r = rint_(100);
        int K = (r < 60) ? 1 : ((r < 90) ? 2 : 3);
        long long lo = tgt;
        if (lo < best_n + 2) lo = best_n + 2;
        long long G0 = lo / (2 * K) + 1;
        long long span = G0 / 30 + 3;
        long long target = G0 + (long long)rint_((int)span);

        int M, Kk, R;
        sample_group(target, &M, &Kk, &R);
        set_group(M, Kk, R);
        if (GG < 2) continue;
        long long N = 2LL * K * GG;
        if (N <= best_n || N > MAXN) continue;

        Cfg cur;
        memset(&cur, 0, sizeof cur);
        cur.K = K;
        random_cfg(&cur);

        Cfg sbest;
        long long sbc = anneal(&cur, RUN_STEPS, &sbest);
        int found = (sbc == 0);

        double sess_end = now_s() + SESSION_S;
        if (sess_end > deadline) sess_end = deadline;
        while (!found && now_s() < sess_end) {
            Cfg st = sbest;
            if (rint_(3) == 0) {
                memset(&st, 0, sizeof st);
                st.K = K;
                random_cfg(&st);
            } else {
                perturb(&st, PERT);
            }
            Cfg rb;
            long long rc = anneal(&st, RUN_STEPS, &rb);
            if (rc < sbc) {
                sbc = rc;
                sbest = rb;
            }
            if (sbc == 0) found = 1;
        }

        if (found) {
            best_n = N;
            best_out = sbest;
            bM = M;
            bK = Kk;
            bR = R;
            have = 1;
            long long base = lo > N ? lo : N;
            tgt = base + N / 200 + 1;
            if (tgt > MAXN / 2) tgt = MAXN / 2;
        } else {
            tgt = best_n + (lo - best_n) * 3 / 4;
            if (tgt < best_n + 2) tgt = best_n + 2;
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    set_group(bM, bK, bR);
    int K = best_out.K, G = best_out.G;
    int n = 2 * K * G;
    printf("%d %ld\n", n, (long)Dd * K * G);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = best_out.P[l][i], s = best_out.S[l][i];
            for (int g = 0; g < G; g++) {
                printf("%d %d\n", i * G + g, (K + j) * G + gmul(g, s));
            }
        }
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions, then the annealing search, with a valid
# fallback at every step.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    safe = max(1.0, min(0.85 * time_limit, time_limit - 7.0))

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        try:
            if n > best_n and lib.is_valid(n, e, d, D):
                best = (n, e)
                best_n = n
        except Exception:
            pass

    if D >= 3:
        try:
            pg = _best_pg(d)
        except Exception:
            pg = None
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Bold search: non-abelian semidirect-product lifts, simulated annealing,
    # sessions aimed at orders just above the best found so far. The start
    # target is a fraction of the Moore bound.
    if D >= 3 and d >= 3:
        start_n = max(best_n + 2, int(0.36 * lib.moore_bound(d, D)))
        remaining = t0 + safe - 2.0 - time.monotonic()
        if remaining >= 3.0:
            try:
                out = lib.run_c(C_SOURCE,
                                [d, D, seed, f"{remaining:.2f}", best_n, start_n],
                                timeout=time_limit - 3.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
