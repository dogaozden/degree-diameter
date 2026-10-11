import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact baselines (safe fallbacks, returned instantly when they are optimal).
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
# C engine (bold variant): general-graph simulated annealing with bitset
# reachability. No group structure is imposed on the final graph. The search
# keeps a valid graph, grows it by adding one vertex per side, and repairs
# the grown graph with 2-switch and add-edge moves that minimise the number
# of ordered vertex pairs at distance > D. Every successful size is saved;
# the largest saved graph is printed at the end, so the output is always valid
# (the starting graph K_{d,d} has diameter 2).
#
# Every few failed growth attempts, a random Cayley-type start on the
# semidirect product Z_m x| Z_k is tried at the target size, which gives the
# repair step a structured starting point.
#
# Vertices: A_i = i (0 <= i < h), B_j = MAXH + j. Output relabels B_j to h + j.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXH 1024
#define MAXV (2 * MAXH)
#define MAXW (MAXV / 64)
#define MAXDEG 32
#define MAXE (MAXH * MAXDEG)
#define EVALS 3000

static int d, D;
static double deadline;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rnd_int(int n) { return (int)(rnd64() % (uint64_t)n); }

static double rnd_unit(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int hcur = 0;
static int deg[MAXV];
static int nbr[MAXV][MAXDEG];
static unsigned char adj[MAXV][MAXV];
static uint64_t RA[MAXV][MAXW], RB[MAXV][MAXW];
static int dA[MAXH], dB[MAXH];

static int sv_h = 0, sv_m = 0;
static int sv_a[MAXE], sv_b[MAXE];

static int popc(uint64_t x) {
    int c = 0;
    while (x) {
        x &= x - 1;
        c++;
    }
    return c;
}

static void add_edge(int a, int b) {
    nbr[a][deg[a]++] = b;
    nbr[b][deg[b]++] = a;
    adj[a][b] = 1;
    adj[b][a] = 1;
}

static void rem_nb(int v, int u) {
    for (int k = 0; k < deg[v]; k++) {
        if (nbr[v][k] == u) {
            nbr[v][k] = nbr[v][--deg[v]];
            return;
        }
    }
}

static void del_edge(int a, int b) {
    rem_nb(a, b);
    rem_nb(b, a);
    adj[a][b] = 0;
    adj[b][a] = 0;
}

static void clear_graph(void) {
    memset(adj, 0, sizeof adj);
    memset(deg, 0, sizeof deg);
}

static void save_graph(void) {
    sv_h = hcur;
    sv_m = 0;
    for (int i = 0; i < hcur; i++) {
        for (int k = 0; k < deg[i]; k++) {
            sv_a[sv_m] = i;
            sv_b[sv_m] = nbr[i][k];
            sv_m++;
        }
    }
}

static void load_graph(int h) {
    clear_graph();
    hcur = h;
    for (int e = 0; e < sv_m; e++) add_edge(sv_a[e], sv_b[e]);
}

/* Returns the number of ordered pairs (u, v), both active, with dist > D. */
static long long eval_cost(void) {
    int W = (MAXH + hcur + 63) >> 6;
    uint64_t (*cur)[MAXW] = RA;
    uint64_t (*nxt)[MAXW] = RB;

    for (int side = 0; side < 2; side++) {
        for (int i = 0; i < hcur; i++) {
            int v = side ? MAXH + i : i;
            for (int w = 0; w < W; w++) cur[v][w] = 0;
            cur[v][v >> 6] |= 1ULL << (v & 63);
        }
    }
    for (int s = 0; s < D; s++) {
        for (int side = 0; side < 2; side++) {
            for (int i = 0; i < hcur; i++) {
                int v = side ? MAXH + i : i;
                for (int w = 0; w < W; w++) nxt[v][w] = cur[v][w];
                for (int k = 0; k < deg[v]; k++) {
                    int u = nbr[v][k];
                    for (int w = 0; w < W; w++) nxt[v][w] |= cur[u][w];
                }
            }
        }
        uint64_t (*t)[MAXW] = cur;
        cur = nxt;
        nxt = t;
    }
    long long bad = 0;
    long long full = 2LL * hcur;
    for (int side = 0; side < 2; side++) {
        for (int i = 0; i < hcur; i++) {
            int v = side ? MAXH + i : i;
            int pc = 0;
            for (int w = 0; w < W; w++) pc += popc(cur[v][w]);
            bad += full - pc;
        }
    }
    return bad;
}

/* Simulated annealing on the graph with fixed sides. Returns 1 if cost 0 reached. */
static int sa_run(long long maxevals) {
    long long cur = eval_cost();
    for (long long it = 0; it < maxevals && cur > 0; it++) {
        if ((it & 15) == 0 && now_s() > deadline) break;
        double T = 0.12 + 1.2 * (1.0 - (double)it / (double)maxevals);

        int na = 0, nbk = 0;
        for (int i = 0; i < hcur; i++) {
            if (deg[i] < d) dA[na++] = i;
            if (deg[MAXH + i] < d) dB[nbk++] = MAXH + i;
        }

        if (na > 0 && nbk > 0 && rnd_unit() < 0.3) {
            int a = dA[rnd_int(na)];
            int b = dB[rnd_int(nbk)];
            if (adj[a][b]) continue;
            add_edge(a, b);
            long long nc = eval_cost();
            long long delta = nc - cur;
            if (delta <= 0 || rnd_unit() < exp(-(double)delta / T)) {
                cur = nc;
            } else {
                del_edge(a, b);
            }
            continue;
        }

        /* 2-switch: keeps all degrees unchanged. */
        int a = -1, a2 = -1;
        for (int tr = 0; tr < 40 && a < 0; tr++) {
            int x = rnd_int(hcur);
            if (deg[x] > 0) a = x;
        }
        for (int tr = 0; tr < 40 && a2 < 0; tr++) {
            int x = rnd_int(hcur);
            if (deg[x] > 0 && x != a) a2 = x;
        }
        if (a < 0 || a2 < 0) continue;
        int b = nbr[a][rnd_int(deg[a])];
        int b2 = nbr[a2][rnd_int(deg[a2])];
        if (b == b2 || adj[a][b2] || adj[a2][b]) continue;

        del_edge(a, b);
        del_edge(a2, b2);
        add_edge(a, b2);
        add_edge(a2, b);
        long long nc = eval_cost();
        long long delta = nc - cur;
        if (delta <= 0 || rnd_unit() < exp(-(double)delta / T)) {
            cur = nc;
        } else {
            del_edge(a, b2);
            del_edge(a2, b);
            add_edge(a, b);
            add_edge(a2, b2);
        }
    }
    return cur == 0;
}

static int gcd_i(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static long long powmod_ll(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int G_M = 1, G_K = 1, G_GP[64];

static int gmul(int x, int y) {
    int a = x / G_K, b = x % G_K;
    int c = y / G_K, e = y % G_K;
    long long t = ((long long)a + (long long)G_GP[b] * (long long)c) % G_M;
    return (int)t * G_K + (b + e) % G_K;
}

/* d-regular bi-Cayley graph on the semidirect product Z_m x| Z_k of order h. */
static void random_group_start(int h) {
    static const int KL[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18,
                             20, 21, 24, 28, 30, 32, 36, 40, 42, 48, 56, 60};
    int nk = (int)(sizeof KL / sizeof KL[0]);
    int k = 1;
    for (int t = 0; t < 30; t++) {
        int c = KL[rnd_int(nk)];
        if (c <= h && h % c == 0) {
            k = c;
            break;
        }
    }
    int m = h / k;
    long long r = 1;
    if (k > 1 && m > 2) {
        for (int t = 0; t < 300; t++) {
            long long c = 2 + rnd_int(m - 2);
            if (gcd_i((int)c, m) == 1 && powmod_ll(c, k, m) == 1 % m) {
                r = c;
                break;
            }
        }
    }
    G_M = m;
    G_K = k;
    long long p = 1 % m;
    for (int b = 0; b < k; b++) {
        G_GP[b] = (int)p;
        p = p * r % m;
    }

    int S[MAXDEG];
    int ns = 0;
    while (ns < d) {
        int s = rnd_int(h);
        int dup = 0;
        for (int i = 0; i < ns; i++)
            if (S[i] == s) dup = 1;
        if (!dup) S[ns++] = s;
    }

    clear_graph();
    hcur = h;
    for (int x = 0; x < h; x++)
        for (int i = 0; i < d; i++)
            add_edge(x, MAXH + gmul(x, S[i]));
}

int main(int argc, char **argv) {
    d = argc > 1 ? atoi(argv[1]) : 3;
    D = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;

    {
        int ch;
        while ((ch = getchar()) != EOF) {
        }
    }

    if (d < 1 || d > MAXDEG || D < 2) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();
    deadline = now_s() + tl;

    /* Valid start: K_{d,d} has diameter 2 <= D. */
    clear_graph();
    hcur = d;
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++)
            add_edge(i, MAXH + j);
    save_graph();

    int step = 1, fails = 0;
    while (now_s() < deadline) {
        if (step > MAXH - 2 - sv_h) step = MAXH - 2 - sv_h;
        if (step < 1) break;
        if (fails % 3 == 2) {
            random_group_start(sv_h + step);
        } else {
            load_graph(sv_h + step);
        }
        if (sa_run(EVALS)) {
            save_graph();
            fails = 0;
            if (step < sv_h / 16) step *= 2;
        } else {
            fails++;
            if (step > 1) step /= 2;
        }
    }

    printf("%d %d\n", 2 * sv_h, sv_m);
    for (int e = 0; e < sv_m; e++) {
        printf("%d %d\n", sv_a[e], sv_h + (sv_b[e] - MAXH));
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions, then the annealing engine. Every returned
# graph is checked with lib.is_valid, and K_{d,d} is kept as the fallback.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
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

    if D >= 4 and time.monotonic() - start < 0.2 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    if D == 2 or d < 3 or d > 30:
        return best

    budget = min(0.85 * time_limit, time_limit - 6.0) - (time.monotonic() - start)
    if budget >= 3.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget - 1.0:.2f}"],
                            timeout=time_limit - 3.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
