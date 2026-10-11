import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact baselines (fallbacks and calibration cases).
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
# C engine: bi-Cayley lifts over semidirect products Z_m x| Z_k, searched by
# simulated annealing on the number of unreached representative pairs.
#
# Vertices: A_{i,g} = i*G+g, B_{j,h} = (K+j)*G+h, and dart (l, i) joins
# A_{i,g} to B_{P[l][i], g*S[l][i]}. Each P[l] is a permutation of 0..K-1,
# so the graph is Dd-regular and bipartite. The group acts on the left, so
# only the 2K class representatives need BFS. Cost 0 means valid.
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
#define PEN 1000

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

static double rfloat(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int Dd = 3, DD = 5;
static int GM = 1, GK = 1, GG = 1;
static long long gpow[MAXK];
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

/* Semidirect product: (a,b)*(c,d) = (a + r^b c, b + d), element coded a*k+b. */
static int gmul(int x, int y) {
    int a = x / GK, b = x % GK;
    int c = y / GK, d = y % GK;
    long long t = ((long long)a + gpow[b] * (long long)c) % GM;
    return (int)t * GK + (b + d) % GK;
}

static int cap = 0, stamp = 0;
static int *adj = NULL, *cnt = NULL, *vis = NULL, *qu = NULL;

static void ensure_cap(int N) {
    if (N <= cap) return;
    free(adj);
    free(cnt);
    free(vis);
    free(qu);
    cap = N;
    adj = malloc(sizeof(int) * (size_t)N * MAXD);
    cnt = malloc(sizeof(int) * (size_t)N);
    vis = calloc((size_t)N, sizeof(int));
    qu = malloc(sizeof(int) * (size_t)N);
    if (!adj || !cnt || !vis || !qu) {
        fprintf(stderr, "out of memory\n");
        exit(1);
    }
    stamp = 0;
}

static void build_adj(const Cfg *c) {
    int K = c->K, G = c->G, N = 2 * K * G;
    ensure_cap(N);
    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = c->P[l][i], s = c->S[l][i];
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                int b = (K + j) * G + gmul(g, s);
                adj[a * MAXD + cnt[a]++] = b;
                adj[b * MAXD + cnt[b]++] = a;
            }
        }
    }
}

/* Returns penalised cost; *rawp receives the number of unreached
   (representative, vertex) pairs. Cost 0 iff the graph is valid. */
static long long eval_cfg(const Cfg *c, long long *rawp) {
    int K = c->K, G = c->G, N = 2 * K * G;
    build_adj(c);
    long long dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < Dd; l1++)
            for (int l2 = l1 + 1; l2 < Dd; l2++)
                if (c->P[l1][i] == c->P[l2][i] && c->S[l1][i] == c->S[l2][i])
                    dup++;
    long long raw = 0;
    for (int r = 0; r < 2 * K; r++) {
        stamp++;
        int head = 0, tail = 0;
        int src = r * G;
        vis[src] = stamp;
        qu[tail++] = src;
        for (int lvl = 0; lvl < DD; lvl++) {
            int end = tail;
            if (head == end) break;
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
    *rawp = raw;
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
}

/* Simulated annealing with geometric cooling over `iters` moves.
   Moves: change one voltage, or (K >= 2) swap two entries of one permutation.
   Leaves the best state in *bestc and returns its penalised cost. */
static long long anneal(Cfg *cur, long iters, Cfg *bestc, long long *bestraw) {
    long long raw;
    long long cc = eval_cfg(cur, &raw);
    long long bc = cc, br = raw;
    *bestc = *cur;
    const double T0 = 4.0, T1 = 0.25;
    int K = cur->K;
    for (long t = 0; t < iters && bc != 0; t++) {
        if ((t & 255) == 0 && now_s() > deadline) break;
        double T = T0 * pow(T1 / T0, (double)t / (double)iters);
        Cfg old = *cur;
        int mv = rint_(10);
        if (K >= 2 && mv < 3) {
            int l = rint_(Dd);
            int i = rint_(K);
            int i2 = rint_(K - 1);
            if (i2 >= i) i2++;
            int tmp = cur->P[l][i];
            cur->P[l][i] = cur->P[l][i2];
            cur->P[l][i2] = tmp;
        } else {
            int l = rint_(Dd);
            int i = rint_(K);
            cur->S[l][i] = rint_(GG);
        }
        long long nraw;
        long long nc = eval_cfg(cur, &nraw);
        long long delta = nc - cc;
        if (delta <= 0 || rfloat() < exp(-(double)delta / T)) {
            cc = nc;
            if (nc < bc) {
                bc = nc;
                br = nraw;
                *bestc = *cur;
            }
        } else {
            *cur = old;
        }
    }
    *bestraw = br;
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

static const int KF[] = {1, 1, 1, 2, 2, 2, 3, 4, 4, 5, 6, 8, 9, 10, 12, 16, 18, 20, 24, 30, 36};

/* Sample a semidirect product Z_m x| Z_k with order m*k near `target`.
   r is chosen uniformly among valid multipliers (r^k = 1, gcd(r,m) = 1);
   if none exists, r = 1 gives the abelian group Z_m x Z_k. */
static void sample_group(long long target, int *oM, int *oK, int *oR) {
    int k = KF[rint_((int)(sizeof(KF) / sizeof(KF[0])))];
    long long m = (target + k - 1) / k;
    if (m < 2) m = 2;
    long long chosen = 1;
    if (k > 1 && m > 2 && rint_(10) < 9) {
        long long cnt_ = 0;
        for (long long c = 2; c < m; c++) {
            if (gcdll(c, m) == 1 && powmod(c, k, m) == 1 % m) {
                cnt_++;
                if (rint_((int)cnt_) == 0) chosen = c;
            }
        }
    }
    *oM = (int)m;
    *oK = k;
    *oR = (int)chosen;
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
    Cfg cur, att, best_cfg;
    memset(&cur, 0, sizeof(cur));
    memset(&att, 0, sizeof(att));
    memset(&best_cfg, 0, sizeof(best_cfg));

    while (now_s() < deadline) {
        int r100 = rint_(100);
        int K = r100 < 60 ? 1 : (r100 < 90 ? 2 : 3);
        long long g0 = (long long)best_n / (2 * K) + 1;
        long long span = g0 / 40 + 2 + (long long)(fails / 15);
        if (span > g0 / 3 + 2) span = g0 / 3 + 2;
        long long G = g0 + (long long)rint_((int)span + 1);
        int M, Kk, R;
        sample_group(G, &M, &Kk, &R);
        set_group(M, Kk, R);
        if (GG > 4000) continue;
        int N = 2 * K * GG;
        if (N <= best_n) continue;

        cur.K = K;
        cur.G = GG;
        random_cfg(&cur);
        long long bestraw = 0;
        long long c = anneal(&cur, 20000, &att, &bestraw);
        if (c == 0) {
            best_n = N;
            best_cfg = att;
            bM = M;
            bK = Kk;
            bR = R;
            have = 1;
            fails = 0;
        } else {
            fails++;
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
# Python glue: exact constructions first, then the C annealer. Every candidate
# is checked with lib.is_valid, and a valid fallback is always kept.
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

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D == 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Annealed bi-Cayley search over semidirect-product lifts, seeded with the
    # best known order as a lower bound.
    if d >= 3 and D >= 3:
        c_budget = deadline - time.monotonic() - 1.0
        if c_budget >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{c_budget:.2f}", best_n],
                                timeout=time_limit - 2.5)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
