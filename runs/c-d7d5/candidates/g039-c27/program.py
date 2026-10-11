import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact baselines (safe fallbacks, always valid).
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
# C engine: EXHAUSTIVE SEMIDIRECT-GROUP ENUMERATION + SIMULATED ANNEALING.
#
# Bold change from the breakout approach: every candidate order G is matched
# against the full list of semidirect products Z_m x|_r Z_k of that order
# (abelian and non-abelian alike), one of which is drawn at random per attempt.
# Each attempt runs a Metropolis simulated annealing over voltage darts
# (S values) and base-side permutations (P swaps). The cost is the number of
# unreached (representative, vertex) pairs within DD steps, plus a penalty per
# duplicate dart. Cost 0 is a valid graph.
#
# Lift: A_{i,g} = i*G+g, B_{j,h} = (K+j)*G+h, dart (l, i) joins A_{i,g} to
# B_{P[l][i], g*S[l][i]}. Each P[l] is a permutation, so the lift is Dd-regular.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK 3
#define MAXD 64
#define MAXKF 64
#define MAXGROUPS 4096
#define MAXORDER 3000
#define PEN 4
#define ITERS 40000

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }

static double rfloat(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int Dd = 3, DD = 3;
static double deadline = 0.0;

/* Current group Z_m x|_r Z_k, element (a,b) coded as a*k+b. */
static int GM = 1, GK = 1, GG = 1;
static long long gpow[MAXKF];

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
    if (b < 0) b += m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Enumerate all semidirect products Z_m x|_r Z_k of order G (k <= MAXKF). */
static int gl_m[MAXGROUPS], gl_k[MAXGROUPS], gl_r[MAXGROUPS];

static int list_groups(int G) {
    int cnt = 0;
    for (int k = 1; k <= MAXKF && k <= G; k++) {
        if (G % k) continue;
        int m = G / k;
        if (m == 1) {
            if (cnt < MAXGROUPS) {
                gl_m[cnt] = 1;
                gl_k[cnt] = k;
                gl_r[cnt] = 0;
                cnt++;
            }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcdll(r, m) != 1) continue;
            if (k == 1) {
                if (r != 1) continue;
            } else {
                if (powmod(r, k, m) != 1 % m) continue;
            }
            if (cnt < MAXGROUPS) {
                gl_m[cnt] = m;
                gl_k[cnt] = k;
                gl_r[cnt] = r;
                cnt++;
            }
        }
    }
    return cnt;
}

/* Lift state: P[l][i] in 0..K-1 (a permutation per l), S[l][i] in the group. */
static int P[MAXD][MAXK], S[MAXD][MAXK];
static int BP[MAXD][MAXK], BS[MAXD][MAXK];
static int FP[MAXD][MAXK], FS[MAXD][MAXK];

static int *g_adj = NULL, *g_cnt = NULL, *g_vis = NULL, *g_q = NULL;
static int capN = 0;
static int stamp = 0;

static void ensure_cap(int N) {
    if (N <= capN) return;
    free(g_adj);
    free(g_cnt);
    free(g_vis);
    free(g_q);
    capN = N;
    g_adj = malloc(sizeof(int) * (size_t)N * (size_t)Dd);
    g_cnt = malloc(sizeof(int) * (size_t)N);
    g_vis = calloc((size_t)N, sizeof(int));
    g_q = malloc(sizeof(int) * (size_t)N);
    if (!g_adj || !g_cnt || !g_vis || !g_q) {
        fprintf(stderr, "out of memory\n");
        exit(1);
    }
    stamp = 0;
}

/* Cost = unreached (representative, vertex) pairs within DD steps + PEN * duplicate darts. */
static long long eval_cost(int K, int G) {
    int N = 2 * K * G;
    memset(g_cnt, 0, sizeof(int) * (size_t)N);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = P[l][i], s = S[l][i];
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
                if (P[l1][i] == P[l2][i] && S[l1][i] == S[l2][i]) dup++;

    long long raw = 0;
    for (int r = 0; r < 2 * K; r++) {
        int src = r * G;
        stamp++;
        if (stamp > 2000000000) {
            memset(g_vis, 0, sizeof(int) * (size_t)capN);
            stamp = 1;
        }
        int head = 0, tail = 0;
        g_vis[src] = stamp;
        g_q[tail++] = src;
        for (int lvl = 0; lvl < DD; lvl++) {
            int end = tail;
            if (head == end) break;
            while (head < end) {
                int u = g_q[head++];
                for (int t = 0; t < Dd; t++) {
                    int v = g_adj[u * Dd + t];
                    if (g_vis[v] != stamp) {
                        g_vis[v] = stamp;
                        g_q[tail++] = v;
                    }
                }
            }
        }
        raw += (long long)(N - tail);
    }
    return raw + (long long)PEN * dup;
}

static void random_state(int K) {
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) P[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = P[l][i];
            P[l][i] = P[l][j];
            P[l][j] = t;
        }
        for (int i = 0; i < K; i++) S[l][i] = rint_(GG);
    }
}

/* Simulated annealing for one (K, group). Leaves best state in BP/BS. */
static long long anneal(int K, int G) {
    int N = 2 * K * G;
    random_state(K);
    long long cur = eval_cost(K, G);
    long long best = cur;
    memcpy(BP, P, sizeof(P));
    memcpy(BS, S, sizeof(S));
    double T0 = 4.0 + 0.005 * (double)N;
    double T1 = 0.2;
    for (long t = 0; t < ITERS && best > 0; t++) {
        if ((t & 127) == 0 && now_s() > deadline) break;
        double T = T0 * pow(T1 / T0, (double)t / (double)ITERS);
        int l = rint_(Dd);
        int i = rint_(K);
        int kind = (K >= 2 && rint_(3) == 0);
        int i2 = -1, oldS = 0;
        if (kind) {
            i2 = rint_(K - 1);
            if (i2 >= i) i2++;
            int tmp = P[l][i];
            P[l][i] = P[l][i2];
            P[l][i2] = tmp;
        } else {
            oldS = S[l][i];
            int s = rint_(GG);
            if (GG > 1) {
                while (s == oldS) s = rint_(GG);
            }
            S[l][i] = s;
        }
        long long nc = eval_cost(K, G);
        long long delta = nc - cur;
        if (delta <= 0 || rfloat() < exp(-(double)delta / T)) {
            cur = nc;
            if (cur < best) {
                best = cur;
                memcpy(BP, P, sizeof(P));
                memcpy(BS, S, sizeof(S));
            }
        } else {
            if (kind) {
                int tmp = P[l][i];
                P[l][i] = P[l][i2];
                P[l][i2] = tmp;
            } else {
                S[l][i] = oldS;
            }
        }
    }
    return best;
}

int main(int argc, char **argv) {
    Dd = argc > 1 ? atoi(argv[1]) : 3;
    DD = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;
    long long min_n = argc > 5 ? atoll(argv[5]) : 0;

    if (Dd < 1 || Dd > MAXD || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 4; w++) rnd();

    double t0 = now_s();
    deadline = t0 + tl;
    long long best_n = min_n;
    int have = 0;
    int fK = 1, fG = 1, fm = 1, fk = 1, fr = 0;

    while (now_s() < deadline) {
        int roll = rint_(100);
        int K = roll < 50 ? 1 : (roll < 85 ? 2 : 3);
        long long g0 = best_n / (2 * K) + 1;
        if (g0 < 2) g0 = 2;
        if (g0 > MAXORDER) break;
        long long span = g0 / 40 + 3;
        long long G = g0 + (long long)rint_((int)span);
        if (G > MAXORDER) continue;
        int cnt = list_groups((int)G);
        if (cnt == 0) continue;
        int pick = rint_(cnt);
        set_group(gl_m[pick], gl_k[pick], gl_r[pick]);
        if (GG < 2) continue;
        ensure_cap(2 * K * (int)G);
        long long bc = anneal(K, (int)G);
        if (bc == 0) {
            best_n = 2LL * K * G;
            have = 1;
            fK = K;
            fG = (int)G;
            fm = gl_m[pick];
            fk = gl_k[pick];
            fr = gl_r[pick];
            memcpy(FP, BP, sizeof(BP));
            memcpy(FS, BS, sizeof(BS));
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    set_group(fm, fk, fr);
    int K = fK, G = fG;
    int N = 2 * K * G;
    long m = (long)Dd * K * G;
    printf("%d %ld\n", N, m);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = FP[l][i], s = FS[l][i];
            for (int g = 0; g < G; g++) {
                printf("%d %d\n", i * G + g, (K + j) * G + gmul(g, s));
            }
        }
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions first, then the C annealer.
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
        try:
            if n > best_n and lib.is_valid(n, e, d, D):
                best = (n, e)
                best_n = n
        except Exception:
            pass

    # Exact constructions.
    if D >= 3:
        try:
            pg = _best_pg(d)
        except Exception:
            pg = None
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < deadline:
        try:
            gq = _best_gq(d)
        except Exception:
            gq = None
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Semidirect-group lift search with simulated annealing in C.
    if d >= 3 and D >= 3:
        c_budget = deadline - time.monotonic() - 2.0
        if c_budget >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{c_budget:.2f}", best_n],
                                timeout=time_limit - 3.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
