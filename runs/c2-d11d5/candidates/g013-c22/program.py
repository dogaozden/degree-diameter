"""Bold revision: exact group-lift search in C, with a new cost function.

Lifts are voltage graphs over semidirect products Z_m x| Z_k. The group acts on each
fibre by left multiplication, so distances from (block, x) equal distances from
(block, identity) after relabelling. Checking the 2K block representatives with BFS is
therefore an exact diameter test for the whole lift. Simulated annealing moves voltages and
block permutations to minimise unreached (representative, vertex) pairs. A ratchet on the
target order keeps only valid successes. Small exact constructions and K_{d,d} remain as
fallbacks, and every returned graph is checked with lib.is_valid.
"""
import itertools
import time

import lib


C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 32
#define MAXK 6
#define MAXNV 16384
#define MAXPW 64

static int d, D;
static double t_end;
static uint64_t rs = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

/* ---- group Z_gm x| Z_gk, element (a,b) coded a*gk+b, (a,b)(c,e) = (a + r^b c, b+e) ---- */
static int gm = 1, gk = 1, gr = 1, go = 1;
static int pw[MAXPW];

static void set_group_pw(void) {
    long long p = 1 % gm;
    for (int b = 0; b < gk; b++) {
        pw[b] = (int)p;
        p = (p * gr) % gm;
    }
}
static int gmul(int x, int y) {
    int a = x / gk, b = x % gk, c = y / gk, e = y % gk;
    long long aa = (a + (long long)pw[b] * c) % gm;
    int bb = (b + e) % gk;
    return (int)(aa * gk + bb);
}
static int ginv(int x) {
    int a = x / gk, b = x % gk;
    int nb = (gk - b) % gk;
    long long na = (gm - ((long long)pw[nb] * a) % gm) % gm;
    return (int)(na * gk + nb);
}
static long long pmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}
static long long ggcd(long long a, long long b) {
    while (b) {
        long long t = a % b;
        a = b;
        b = t;
    }
    return a;
}
static int sample_group(long target) {
    static const int k2s[11] = {1, 1, 2, 2, 3, 4, 5, 6, 8, 10, 12};
    for (int tries = 0; tries < 200; tries++) {
        int k2 = k2s[rndint(11)];
        long m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        long long r = -1;
        if (k2 == 1) {
            r = 1 % m;
        } else if (k2 == 2 && rndint(3) == 0) {
            r = m - 1;
        } else {
            for (int t = 0; t < 300; t++) {
                long long c = (m > 2) ? 2 + rndint((int)(m - 2)) : 1;
                if (ggcd(c, m) == 1 && pmod(c, k2, m) == 1 % m) {
                    r = c;
                    break;
                }
            }
        }
        if (r < 0) continue;
        if (ggcd(r, m) != 1 || pmod(r, k2, m) != 1 % m) continue;
        gm = (int)m;
        gk = k2;
        gr = (int)r;
        go = gm * gk;
        set_group_pw();
        return 1;
    }
    return 0;
}

/* ---- lift: K blocks per side, d layers; layer l maps A-block i to B-block pin[l][i] ---- */
static int K = 1, N = 2;
static int pin[MAXD][MAXK];
static int sv[MAXD][MAXK];
static int adj[MAXNV * MAXD];
static int vis[MAXNV];
static int qb[MAXNV];
static int vstamp = 0;

/* A_{i,x} -- B_{j, x s} and B_{j,y} -- A_{i, y s^-1} in layer l. */
static void set_dart(int l, int i) {
    int j = pin[l][i], s = sv[l][i], si = ginv(s);
    int A0 = i * go, B0 = (K + j) * go;
    for (int x = 0; x < go; x++) {
        adj[(A0 + x) * d + l] = B0 + gmul(x, s);
        adj[(B0 + x) * d + l] = A0 + gmul(x, si);
    }
}

static void random_state(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) pin[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int t = rndint(i + 1);
            int tmp = pin[l][i];
            pin[l][i] = pin[l][t];
            pin[l][t] = tmp;
        }
        for (int i = 0; i < K; i++) sv[l][i] = rndint(go);
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) set_dart(l, i);
}

static long dupcount(void) {
    long c = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (pin[l1][i] == pin[l2][i] && sv[l1][i] == sv[l2][i]) c++;
    return c;
}

/* Number of vertices within distance D of src (src included). */
static int bfs_reach(int src) {
    if (++vstamp == 0x7fffffff) {
        memset(vis, 0, sizeof vis);
        vstamp = 1;
    }
    int head = 0, tail = 0;
    qb[tail++] = src;
    vis[src] = vstamp;
    for (int depth = 0; depth < D && head < tail; depth++) {
        int end = tail;
        while (head < end) {
            int v = qb[head++];
            const int *nb = adj + (size_t)v * d;
            for (int l = 0; l < d; l++) {
                int u = nb[l];
                if (vis[u] != vstamp) {
                    vis[u] = vstamp;
                    qb[tail++] = u;
                }
            }
        }
    }
    return tail;
}

/* Exact: by the left-multiplication symmetry, pairs are covered by the 2K block representatives. */
static long eval_cost(void) {
    long c = 0;
    for (int b = 0; b < 2 * K; b++) c += N - bfs_reach(b * go);
    c += (long)N * dupcount();
    return c;
}

/* One attempt: random restarts with simulated annealing until deadline. 1 = zero cost found. */
static int attempt(double deadline) {
    while (now() < deadline) {
        random_state();
        long cost = eval_cost();
        if (cost == 0) return 1;
        double T0 = 1.0 + 0.05 * (double)cost, T = T0;
        long bestc = cost;
        int since = 0;
        for (int it = 0; it < 30000 && since < 2000; it++) {
            if ((it & 7) == 0 && now() > deadline) break;
            if (K >= 2 && rnd01() < 0.3) {
                int l = rndint(d), i1 = rndint(K), i2 = rndint(K - 1);
                if (i2 >= i1) i2++;
                int t = pin[l][i1];
                pin[l][i1] = pin[l][i2];
                pin[l][i2] = t;
                set_dart(l, i1);
                set_dart(l, i2);
                long c2 = eval_cost();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                    cost = c2;
                } else {
                    t = pin[l][i1];
                    pin[l][i1] = pin[l][i2];
                    pin[l][i2] = t;
                    set_dart(l, i1);
                    set_dart(l, i2);
                }
            } else {
                int l = rndint(d), i = rndint(K);
                int old = sv[l][i], nw = rndint(go);
                if (nw == old) continue;
                sv[l][i] = nw;
                set_dart(l, i);
                long c2 = eval_cost();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                    cost = c2;
                } else {
                    sv[l][i] = old;
                    set_dart(l, i);
                }
            }
            if (cost == 0) return 1;
            if (cost < bestc) {
                bestc = cost;
                since = 0;
            } else {
                since++;
            }
            T *= 0.998;
            if (T < 0.3) T = 0.3;
        }
    }
    return 0;
}

static int bK = 1, bgm = 1, bgk = 1, bgr = 1, bgo = 1, bN = 0;
static int bpin[MAXD][MAXK], bsv[MAXD][MAXK];

static void save_best(void) {
    bK = K;
    bgm = gm;
    bgk = gk;
    bgr = gr;
    bgo = go;
    bN = N;
    memcpy(bpin, pin, sizeof pin);
    memcpy(bsv, sv, sizeof sv);
}

static void print_best(void) {
    gm = bgm;
    gk = bgk;
    gr = bgr;
    go = bgo;
    set_group_pw();
    long m = (long)bK * go * d;
    printf("%d %ld\n", bN, m);
    for (int i = 0; i < bK; i++)
        for (int x = 0; x < go; x++) {
            int u = i * go + x;
            for (int l = 0; l < d; l++) {
                int v = (bK + bpin[l][i]) * go + gmul(x, bsv[l][i]);
                printf("%d %d\n", u, v);
            }
        }
}

static int pick_k(const int *trials, const int *wins) {
    if (rnd01() < 0.25) return 1 + rndint(5);
    int bestk = 1;
    double bv = -1.0;
    for (int k = 1; k <= 5; k++) {
        double v = (wins[k] + 1.0) / (trials[k] + 2.0) + 0.05 * rnd01();
        if (v > bv) {
            bv = v;
            bestk = k;
        }
    }
    return bestk;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit minN\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long minN = atol(argv[5]);
    double t0 = now();
    t_end = t0 + limit * 0.92 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    double moore = 0.0, pm = 1.0;
    for (int i = 0; i < D; i++) {
        moore += pm;
        pm *= (d - 1);
        if (moore > 1e9) break;
    }
    moore *= 2.0;

    long best_n = minN;
    int found = 0;
    double goal = (double)minN * 1.05 + 2.0;
    int trials[MAXK + 1] = {0}, wins[MAXK + 1] = {0};

    while (now() < t_end - 0.1) {
        double rem = t_end - now();
        int k = pick_k(trials, wins);
        long target = (long)ceil(goal / (2.0 * k)) + rndint(3);
        if (target < 2) target = 2;
        if (!sample_group(target)) {
            goal = (double)best_n * 1.01 + 2.0;
            continue;
        }
        long Nc = 2L * k * go;
        if (Nc <= best_n) {
            goal = (double)best_n * 1.02 + 2.0;
            continue;
        }
        if (Nc > MAXNV || (double)Nc > moore) {
            double g2 = goal * 0.97;
            double floorv = (double)best_n * 1.01 + 2.0;
            goal = g2 > floorv ? g2 : floorv;
            continue;
        }
        K = k;
        N = (int)Nc;
        trials[k]++;
        double slice = rem / 4.0;
        if (slice < 3.0) slice = rem;
        double dl = now() + slice;
        if (dl > t_end) dl = t_end;
        if (attempt(dl)) {
            wins[k]++;
            save_best();
            best_n = N;
            found = 1;
            goal = (double)N * 1.02 + 2.0;
        } else {
            double g2 = goal * 0.97;
            double floorv = (double)best_n + 2.0;
            goal = g2 > floorv ? g2 : floorv;
        }
    }
    if (found) print_best();
    else printf("0 0\n");
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Small exact constructions (kept as strong fallbacks).
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


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    total = max(1.0, 0.85 * time_limit - 1.5)
    final = t0 + total

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions.
    if D >= 3:
        try:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
                if D == 3 and lib.is_prime_power(d - 1):
                    return best
        except Exception:
            pass
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass
    if D == 4 and time.monotonic() < final:
        try:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    consider(*_gq_w(q))
                    break
        except Exception:
            pass

    # Main search: C group-lift annealer with an exact representative-BFS cost.
    remaining = final - time.monotonic() - 1.0
    if remaining > 2.0 and d >= 2 and D >= 2:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2), best_n],
                             timeout=remaining + 2.0)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
