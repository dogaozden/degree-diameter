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
# C engine: bi-Cayley (group lift) search by simulated annealing.
#
# This replaces the breakout search with a different optimiser:
#   - K in {1,2,3} base vertices per side, semidirect groups Z_m x| Z_k,
#   - cost = unreached (representative, vertex) pairs within DD steps
#            + PEN * duplicate darts, evaluated with plain BFS from the
#            2K orbit representatives (left multiplication is a symmetry),
#   - Metropolis annealing with moves: change one voltage, or swap two
#     entries of a layer permutation,
#   - near-miss restarts, and a time-based floor relaxation so the search
#     can descend from a high floor to a reachable order.
#
# Vertices: A_{i,g} = i*G+g, B_{j,h} = (K+j)*G+h, dart (l, i) joins
# A_{i,g} to B_{P[l][i], g*S[l][i]}. Output is valid when cost is 0.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define MAXD 16
#define MAXK 4
#define MAXN 24000
#define PEN 4
#define ITERS 60000
#define NEAR_PCT 50

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

static double urand(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int Dd = 3, DD = 3;
static int GM = 1, GK = 1, GG = 1;
static int gpow[64];
static double deadline = 0.0;

static int adj[MAXN * MAXD];
static int ncnt[MAXN];
static int vis[MAXN];
static int qu[MAXN];
static int stamp = 0;

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

/* (a,b)*(c,d) = (a + r^b c, b + d), element coded as a*GK + b. */
static int gmul(int x, int y) {
    int a = x / GK, b = x % GK;
    int c = y / GK, d = y % GK;
    long long t = ((long long)a + (long long)gpow[b] * (long long)c) % GM;
    return (int)t * GK + (b + d) % GK;
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

/* Unweighted cost: unreached (rep, vertex) pairs within DD + PEN * duplicates. */
static long long cost_eval(const Cfg *c) {
    int K = c->K, G = c->G, N = 2 * K * G;
    memset(ncnt, 0, sizeof(int) * (size_t)N);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = c->P[l][i], s = c->S[l][i];
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                int b = (K + j) * G + gmul(g, s);
                adj[a * MAXD + ncnt[a]++] = b;
                adj[b * MAXD + ncnt[b]++] = a;
            }
        }
    }
    long long dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < Dd; l1++)
            for (int l2 = l1 + 1; l2 < Dd; l2++)
                if (c->P[l1][i] == c->P[l2][i] && c->S[l1][i] == c->S[l2][i])
                    dup++;

    long long raw = 0;
    for (int r = 0; r < 2 * K; r++) {
        stamp++;
        int src = r * G;
        int head = 0, tail = 0;
        vis[src] = stamp;
        qu[tail++] = src;
        for (int lvl = 0; lvl < DD && head < tail; lvl++) {
            int end = tail;
            while (head < end) {
                int u = qu[head++];
                for (int t = 0; t < Dd; t++) {
                    int v = adj[u * MAXD + t];
                    if (vis[v] != stamp) {
                        vis[v] = stamp;
                        qu[tail++] = v;
                    }
                }
            }
        }
        raw += (long long)(N - tail);
    }
    return raw + (long long)PEN * dup;
}

/* Metropolis annealing on the cost. Returns best cost; *out holds that state. */
static long long anneal(Cfg *c, long iters, double scale, Cfg *out) {
    int K = c->K;
    long long cur = cost_eval(c);
    long long bc = cur;
    Cfg bcfg = *c;
    double T0 = scale * (0.02 * (double)cur + 0.3);
    double T1 = 0.1;
    if (T0 < T1 * 1.5) T0 = T1 * 1.5;
    for (long t = 0; t < iters && bc != 0; t++) {
        if ((t & 63) == 0 && now_s() > deadline) break;
        double T = T0 * pow(T1 / T0, (double)t / (double)iters);
        int l = rint_(Dd);
        int i = rint_(K);
        int kind = (K >= 2 && rint_(3) == 0);
        int i2 = 0, old = 0, ns = 0;
        if (kind) {
            i2 = rint_(K - 1);
            if (i2 >= i) i2++;
            int tmp = c->P[l][i];
            c->P[l][i] = c->P[l][i2];
            c->P[l][i2] = tmp;
        } else {
            old = c->S[l][i];
            ns = rint_(GG);
            if (ns == old) continue;
            c->S[l][i] = ns;
        }
        long long nc = cost_eval(c);
        long long dl = nc - cur;
        if (dl <= 0 || urand() < exp(-(double)dl / T)) {
            cur = nc;
            if (cur < bc) {
                bc = cur;
                bcfg = *c;
            }
        } else {
            if (kind) {
                int tmp = c->P[l][i];
                c->P[l][i] = c->P[l][i2];
                c->P[l][i2] = tmp;
            } else {
                c->S[l][i] = old;
            }
        }
    }
    *out = bcfg;
    return bc;
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
    for (int w = 0; w < 8; w++) rnd();

    double t0 = now_s();
    deadline = t0 + tl;
    int best_n = min_n;
    int have = 0;
    Cfg best_cfg;
    memset(&best_cfg, 0, sizeof(best_cfg));
    int bM = 1, bK = 1, bR = 1;
    int fails = 0;
    double last_progress = t0;

    int have_near = 0;
    Cfg near;
    memset(&near, 0, sizeof(near));
    int nM = 1, nK = 1, nR = 1, nN = 0;
    long long nraw = 0;

    while (now_s() < deadline) {
        double now = now_s();
        /* Without any success for a while, lower the floor a little so the
           search can descend to an order it can actually reach. */
        if (!have && now - last_progress > 6.0) {
            int nb = best_n - best_n / 25 - 1;
            best_n = nb < 2 ? 2 : nb;
            last_progress = now;
        }

        Cfg cur;
        memset(&cur, 0, sizeof(cur));
        int M = 1, Kk = 1, R = 1;
        double scale = 1.0;
        int use_near = have_near && nN > best_n && (rint_(100) < NEAR_PCT);
        if (use_near) {
            cur = near;
            M = nM;
            Kk = nK;
            R = nR;
            set_group(M, Kk, R);
            cur.G = GG;
            for (int t = 0; t < 2; t++) {
                int l = rint_(Dd);
                int i = rint_(cur.K);
                cur.S[l][i] = rint_(GG);
            }
            scale = 0.3;
        } else {
            int K;
            int r = rint_(10);
            K = r < 6 ? 1 : (r < 9 ? 2 : 3);
            long long g0 = (long long)best_n / (2 * K) + 1;
            long long span = g0 / 20 + 4 + (long long)(fails / 30) * (g0 / 40 + 1);
            if (span > g0 / 3 + 6) span = g0 / 3 + 6;
            long long g = g0 + (long long)rint_((int)span + 1);
            sample_group(g, &M, &Kk, &R);
            set_group(M, Kk, R);
            if (2LL * K * GG > MAXN) continue;
            cur.K = K;
            random_cfg(&cur);
        }

        int N = 2 * cur.K * GG;
        if (N <= best_n) continue;

        Cfg res;
        memset(&res, 0, sizeof(res));
        long long c = anneal(&cur, ITERS, scale, &res);
        if (c == 0) {
            best_n = N;
            best_cfg = res;
            bM = M;
            bK = Kk;
            bR = R;
            have = 1;
            have_near = 0;
            fails = 0;
            last_progress = now_s();
        } else {
            fails++;
            if (!have_near || c <= nraw) {
                near = res;
                nM = M;
                nK = Kk;
                nR = R;
                nN = N;
                nraw = c;
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
# Python glue: exact constructions first, then the annealing search in C.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(3.0, min(0.85 * time_limit, time_limit - 6.0))

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

    # Annealing search over group lifts. The floor starts near a fraction of
    # the Moore bound and is relaxed inside C if nothing is found, so the
    # search can still return something better than the exact baseline.
    if d >= 3 and D >= 3:
        c_budget = deadline - time.monotonic() - 1.5
        if c_budget >= 2.0:
            floor = max(best_n, int(0.30 * lib.moore_bound(d, D)))
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{c_budget:.2f}", floor],
                                timeout=time_limit - 3.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
