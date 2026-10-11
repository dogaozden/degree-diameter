import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact baselines (kept as safe starting points).
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
# C engine: bi-Cayley voltage search over semidirect products Z_m x| Z_k.
#
# Vertices: A_{i,g} = i*G+g (side A, block i), B_{j,h} = (K+j)*G+h (side B).
# Dart (l, i) joins A_{i,g} to B_{P[l][i], g*S[l][i]}; each P[l] is a
# permutation of 0..K-1, so the graph is Dd-regular and bipartite.
# Left translation by group elements is an automorphism, so the diameter
# condition reduces to one BFS of depth DD from each of the 2K block
# representatives. Cost = total unreached pairs + PEN * duplicate darts.
# Search: simulated annealing with periodic reheats from the best state,
# applied to many group orders just above the current record, with a
# random choice among ALL valid semidirect products of each order.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define MAXD 64
#define MAXK 2
#define MAXG 15000
#define PEN 50
#define T0 2.0
#define TMIN 0.2
#define PERIOD 30000.0
#define MAXCAND 600

typedef struct {
    int K;
    int P[MAXD][MAXK];
    int S[MAXD][MAXK];
} State;

static uint64_t rs = 1;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndi(int n) { return (int)(rnd64() % (uint64_t)n); }

static double rndu(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int Dd = 3, DD = 3;
static double deadline = 0.0;

/* Current group: Z_GM x|_GR Z_GK, order G = GM*GK, element a*GK+b. */
static int GM = 1, GK = 1, GR = 0, G = 1;
static int gpow[4096];

static void set_group(int m, int k, int r) {
    GM = m;
    GK = k;
    GR = r;
    G = m * k;
    long long p = 1 % m;
    for (int b = 0; b < k; b++) {
        gpow[b] = (int)p;
        p = (p * r) % m;
    }
}

static inline int gmul(int x, int y) {
    int a = x / GK, b = x - a * GK;
    int c = y / GK, d = y - c * GK;
    int t = (a + (int)(((long long)gpow[b] * c) % GM)) % GM;
    int e = (b + d) % GK;
    return t * GK + e;
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

static int *adj = NULL, *cnt = NULL, *vis = NULL, *que = NULL;
static int capN = 0, stamp = 0;

static void ensure(int N) {
    if (N <= capN) return;
    free(adj);
    free(cnt);
    free(vis);
    free(que);
    capN = N;
    adj = malloc(sizeof(int) * (size_t)N * (size_t)Dd);
    cnt = malloc(sizeof(int) * (size_t)N);
    vis = calloc((size_t)N, sizeof(int));
    que = malloc(sizeof(int) * (size_t)N);
    if (!adj || !cnt || !vis || !que) {
        fprintf(stderr, "out of memory\n");
        exit(1);
    }
    stamp = 0;
}

static long long evaluate(const State *s) {
    int K = s->K, N = 2 * K * G;
    ensure(N);
    for (int v = 0; v < N; v++) cnt[v] = 0;
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = s->P[l][i], sv = s->S[l][i];
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                int b = (K + j) * G + gmul(g, sv);
                adj[a * Dd + cnt[a]++] = b;
                adj[b * Dd + cnt[b]++] = a;
            }
        }
    }
    long long dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < Dd; l1++)
            for (int l2 = l1 + 1; l2 < Dd; l2++)
                if (s->P[l1][i] == s->P[l2][i] && s->S[l1][i] == s->S[l2][i])
                    dup++;

    long long unreached = 0;
    for (int r = 0; r < 2 * K; r++) {
        stamp++;
        int head = 0, tail = 0;
        int src = r * G;
        vis[src] = stamp;
        que[tail++] = src;
        for (int lvl = 0; lvl < DD; lvl++) {
            int end = tail;
            if (head == end) break;
            while (head < end) {
                int u = que[head++];
                for (int t = 0; t < Dd; t++) {
                    int v = adj[u * Dd + t];
                    if (vis[v] != stamp) {
                        vis[v] = stamp;
                        que[tail++] = v;
                    }
                }
            }
        }
        unreached += (long long)(N - tail);
    }
    return unreached + (long long)PEN * dup;
}

static void random_state(State *s, int K) {
    s->K = K;
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) s->P[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndi(i + 1);
            int t = s->P[l][i];
            s->P[l][i] = s->P[l][j];
            s->P[l][j] = t;
        }
        for (int i = 0; i < K; i++) s->S[l][i] = rndi(G);
    }
}

/* Simulated annealing on the current group. Returns the best cost; *best
   holds the corresponding state. Stops early at cost 0. */
static long long anneal(State *cur, State *best, double seconds) {
    double t_end = now_s() + seconds;
    if (t_end > deadline) t_end = deadline;
    long long c = evaluate(cur);
    long long bc = c;
    *best = *cur;
    double decay = pow(TMIN / T0, 1.0 / PERIOD);
    double T = T0;
    long it = 0;
    while (bc > 0) {
        it++;
        if ((it & 127) == 0 && now_s() > t_end) break;
        int K = cur->K;
        int l = rndi(Dd), i = rndi(K);
        int kind = (K >= 2 && rndi(3) == 0);
        int i2 = 0, old = 0;
        if (kind) {
            i2 = rndi(K - 1);
            if (i2 >= i) i2++;
            int t = cur->P[l][i];
            cur->P[l][i] = cur->P[l][i2];
            cur->P[l][i2] = t;
        } else {
            old = cur->S[l][i];
            cur->S[l][i] = rndi(G);
        }
        long long nc = evaluate(cur);
        long long delta = nc - c;
        if (delta <= 0 || rndu() < exp(-(double)delta / T)) {
            c = nc;
            if (c < bc) {
                bc = c;
                *best = *cur;
            }
        } else {
            if (kind) {
                int t = cur->P[l][i];
                cur->P[l][i] = cur->P[l][i2];
                cur->P[l][i2] = t;
            } else {
                cur->S[l][i] = old;
            }
        }
        T *= decay;
        if (T < TMIN) {
            T = T0;
            *cur = *best;
            c = bc;
        }
    }
    return bc;
}

static int cand_m[MAXCAND], cand_k[MAXCAND], cand_r[MAXCAND];

/* All semidirect products Z_m x| Z_k of order Gt with r^k = 1 mod m, gcd(r,m)=1. */
static int enum_groups(long long Gt) {
    int nc = 0;
    for (long long k = 1; k <= Gt && nc < MAXCAND; k++) {
        if (Gt % k) continue;
        if (k > 4000) continue;
        long long m = Gt / k;
        if (k == 1 || m == 1) {
            cand_m[nc] = (int)m;
            cand_k[nc] = (int)k;
            cand_r[nc] = 0;
            nc++;
            continue;
        }
        for (long long r = 1; r < m && nc < MAXCAND; r++) {
            if (gcdll(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            cand_m[nc] = (int)m;
            cand_k[nc] = (int)k;
            cand_r[nc] = (int)r;
            nc++;
        }
    }
    return nc;
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
    rs = (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 8; w++) rnd64();

    double t0 = now_s();
    deadline = t0 + tl;

    int have = 0;
    State bestS;
    int bestK = 1, bestM = 1, bestKk = 1, bestR = 0;
    memset(&bestS, 0, sizeof(bestS));

    while (1) {
        double remaining = deadline - now_s();
        if (remaining < 0.2) break;

        int K = (rndi(100) < 75) ? 1 : 2;
        long long Gmin = min_n / (2LL * K) + 1;
        if (Gmin < 2) Gmin = 2;
        long long span = Gmin / 40 + 4;
        long long Gt = Gmin + (long long)rndi((int)span);
        if (Gt > MAXG) break;

        int nc = enum_groups(Gt);
        if (nc == 0) continue;
        int idx = rndi(nc);
        set_group(cand_m[idx], cand_k[idx], cand_r[idx]);

        double slice = remaining / 8.0;
        if (slice > 6.0) slice = 6.0;
        if (slice < 0.5) slice = 0.5;
        if (slice > remaining) slice = remaining;

        State cur, bst;
        random_state(&cur, K);
        long long c = anneal(&cur, &bst, slice);
        if (c == 0) {
            min_n = 2LL * K * G;
            bestS = bst;
            bestK = K;
            bestM = GM;
            bestKk = GK;
            bestR = GR;
            have = 1;
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    set_group(bestM, bestKk, bestR);
    int K = bestS.K;
    int N = 2 * K * G;
    printf("%d %ld\n", N, (long)Dd * K * G);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = bestS.P[l][i], sv = bestS.S[l][i];
            for (int g = 0; g < G; g++) {
                printf("%d %d\n", i * G + g, (K + j) * G + gmul(g, sv));
            }
        }
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions, then one annealing run with the rest of
# the time. Every output is validated; the exact baseline is the fallback.
# ----------------------------------------------------------------------------

def _search(d, D, seed, budget, min_n):
    """One C search run. Returns (n, edges) if it produced a valid larger graph, else None."""
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", min_n],
                        timeout=budget + 4.0)
        n, e = lib.parse_graph_text(out)
        if n > min_n and lib.is_valid(n, e, d, D):
            return n, e
    except Exception:
        pass
    return None


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

    # Annealing over semidirect-product voltage graphs, seeded above the baseline.
    if d >= 3 and D >= 3:
        remaining = deadline - time.monotonic() - 1.0
        if remaining >= 3.0:
            res = _search(d, D, seed, remaining, best_n)
            if res is not None:
                consider(*res)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
