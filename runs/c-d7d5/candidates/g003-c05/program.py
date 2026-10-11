import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Safe baseline families (unchanged from the parent).
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
# Main search, in C.
#
# Bi-Cayley lift over G = Z_m x| Z_k2 with K base vertices per side. Each of the
# d layers is a permutation P_l of the K base vertices with one voltage per
# dart, so every vertex has degree d. Vertices: A_{i,g} = i*G+g,
# B_{j,h} = (K+j)*G+h, and dart (i,j,s) joins A_{i,g} to B_{j,g*s}. Left
# multiplication is an automorphism, so BFS from the 2K block representatives
# decides the diameter.
#
# New in this version:
#  * Blame-guided moves. Each cost evaluation records, per base block, how many
#    vertices are unreached from the representatives. Moves are then biased
#    toward darts that touch the blocks with the most failures, instead of being
#    uniform over all darts.
#  * Iterated local search. If an anneal from a random start ends with cost > 0,
#    we restart from the best near-solution of that group after a small random
#    kick of a few voltages, and re-anneal. This runs a few times per group
#    before moving on to a new group.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 64
#define MAXK 8
#define MAXB 16
#define PEN 1000
#define ITERS 8000
#define PERT_ROUNDS 4
#define PERT_ITERS 3000
#define PERT_KICK 3

typedef struct {
    int K, M, K2, R, G;
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
static int GM = 1, GK2 = 1, GG = 1;
static int gpow[64];

static void set_group(int M, int K2, int R) {
    GM = M;
    GK2 = K2;
    GG = M * K2;
    long long p = 1 % M;
    for (int b = 0; b < K2; b++) {
        gpow[b] = (int)p;
        p = (p * R) % M;
    }
}

/* (a,b)*(c,d) = (a + r^b c, b + d), element coded as a*K2 + b. */
static int gmul(int x, int y) {
    int a = x / GK2, b = x % GK2;
    int c = y / GK2, d = y % GK2;
    long long t = ((long long)a + (long long)gpow[b] * (long long)c) % GM;
    return (int)t * GK2 + (b + d) % GK2;
}

static int cap = 0;
static int *g_adj = NULL, *g_cnt = NULL, *g_vis = NULL, *g_q = NULL;
static int g_stamp = 0;
static int blame[MAXB];

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
}

/* Cost = unreached (rep, vertex) pairs within DD, plus PEN per duplicate dart.
   Also fills blame[b] = unreached count landing in base block b (0..2K-1). */
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

    memset(blame, 0, sizeof blame);
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
        if (tail < N) {
            for (int v = 0; v < N; v++) {
                if (g_vis[v] != g_stamp) {
                    blame[v / G]++;
                    unreached++;
                }
            }
        }
    }
    return (int)unreached + PEN * dup;
}

static Cfg cur, best_cfg;
static Cfg arun_cfg;
static int arun_cost = 0;
static int have_best = 0, best_n = 0;
static double deadline = 0.0;
static int timed_out = 0;

static void random_cfg(Cfg *c) {
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < c->K; i++) c->P[l][i] = i;
        for (int i = c->K - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = c->P[l][i];
            c->P[l][i] = c->P[l][j];
            c->P[l][j] = t;
        }
        for (int i = 0; i < c->K; i++) c->S[l][i] = rint_(c->G);
    }
}

/* Blame-guided choice of a dart (layer, base vertex). Half the time, pick a
   base block with probability proportional to its blame and choose a dart
   that touches it; otherwise choose uniformly. */
static void pick_dart(int *pl, int *pi) {
    int K = cur.K, total = 0;
    for (int b = 0; b < 2 * K; b++) total += blame[b];
    if (total > 0 && rint_(2) == 0) {
        int x = rint_(total), b = 0;
        while (x >= blame[b]) {
            x -= blame[b];
            b++;
        }
        int l = rint_(Dd);
        int i = -1;
        if (b < K) {
            i = b;
        } else {
            int j = b - K;
            for (int t = 0; t < K; t++) {
                if (cur.P[l][t] == j) {
                    i = t;
                    break;
                }
            }
            if (i < 0) i = rint_(K);
        }
        *pl = l;
        *pi = i;
    } else {
        *pl = rint_(Dd);
        *pi = rint_(K);
    }
}

/* Anneal from the current state. Records the lowest-cost state seen in
   arun_cfg / arun_cost. Returns the final cost. */
static int anneal(long iters, double T0) {
    int c = cost_of(&cur);
    arun_cost = c;
    arun_cfg = cur;
    for (long t = 0; t < iters && c != 0; t++) {
        if ((t & 255) == 0 && now_s() > deadline) {
            timed_out = 1;
            break;
        }
        double temp = T0 * (1.0 - (double)t / (double)iters) + 0.05;
        int l = 0, i = 0;
        pick_dart(&l, &i);
        int swap_kind = (cur.K >= 2 && rint_(5) == 0);
        int old_s = 0, i2 = 0;
        if (swap_kind) {
            i2 = rint_(cur.K - 1);
            if (i2 >= i) i2++;
            int tmp = cur.P[l][i];
            cur.P[l][i] = cur.P[l][i2];
            cur.P[l][i2] = tmp;
        } else {
            old_s = cur.S[l][i];
            cur.S[l][i] = rint_(cur.G);
        }
        int c2 = cost_of(&cur);
        if (c2 <= c || rdbl() < exp(-(double)(c2 - c) / temp)) {
            c = c2;
            if (c < arun_cost) {
                arun_cost = c;
                arun_cfg = cur;
            }
        } else {
            if (swap_kind) {
                int tmp = cur.P[l][i];
                cur.P[l][i] = cur.P[l][i2];
                cur.P[l][i2] = tmp;
            } else {
                cur.S[l][i] = old_s;
            }
        }
    }
    return c;
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

static const int K2S[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};

static int sample_group(long long target, int *oM, int *oK2, int *oR) {
    for (int tries = 0; tries < 200; tries++) {
        int k2 = K2S[rint_(20)];
        long long m = target / k2;
        if (m < 2) m = 2;
        int r = 1;
        if (k2 > 1 && m > 2) {
            for (int t = 0; t < 60; t++) {
                long long c = 2 + rint_((int)(m - 2));
                if (gcdll(c, m) == 1 && powmod(c, k2, m) == 1 % m) {
                    r = (int)c;
                    break;
                }
            }
        }
        *oM = (int)m;
        *oK2 = k2;
        *oR = r;
        return 1;
    }
    return 0;
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
    best_n = min_n;
    static const int Kchoices[6] = {1, 2, 2, 3, 3, 4};

    while (!timed_out && now_s() < deadline) {
        int Kc = Kchoices[rint_(6)];
        long long base = best_n / (2 * Kc);
        long long span = base / 8 + 1;
        long long target = base + 1 + rint_((int)span);
        if (target < 2) target = 2;

        int M, K2, R;
        sample_group(target, &M, &K2, &R);
        set_group(M, K2, R);
        if (2 * Kc * GG <= best_n) continue;

        cur.K = Kc;
        cur.G = GG;
        cur.M = M;
        cur.K2 = K2;
        cur.R = R;
        ensure_cap(2 * Kc * GG);
        random_cfg(&cur);

        anneal(ITERS, 2.0);
        Cfg gcfg = arun_cfg;
        int gcost = arun_cost;

        /* Iterated local search: kick the group's best near-solution and re-anneal. */
        for (int round = 0; round < PERT_ROUNDS && gcost != 0 && !timed_out; round++) {
            cur = gcfg;
            for (int k = 0; k < PERT_KICK; k++) {
                int l = rint_(Dd), i = rint_(cur.K);
                cur.S[l][i] = rint_(cur.G);
            }
            anneal(PERT_ITERS, 0.8);
            if (arun_cost < gcost) {
                gcost = arun_cost;
                gcfg = arun_cfg;
            }
        }

        if (gcost == 0) {
            int n = 2 * Kc * GG;
            if (n > best_n) {
                best_n = n;
                best_cfg = gcfg;
                have_best = 1;
            }
        }
    }

    if (!have_best) {
        printf("0 0\n");
        return 0;
    }
    set_group(best_cfg.M, best_cfg.K2, best_cfg.R);
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
# Python glue: exact constructions, then the C search from the best known graph.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(4.0, min(0.85 * time_limit, time_limit - 6.0))

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

    # Exact constructions: return immediately for calibration-style cases.
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

    # Main search in C, seeded with the best known order as a lower bound.
    if d >= 3 and D >= 3:
        c_budget = deadline - time.monotonic() - 2.0
        if c_budget >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{c_budget:.2f}", best_n],
                                timeout=time_limit - 4.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
