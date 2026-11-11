"""Semidirect Haar lifts for the bipartite degree-diameter problem.

Change from the parent: instead of only the affine groups F_q x| H (prime-power q),
this version searches the wider family of semidirect products Z_m x|_r Z_k with
k <= 16 and r^k = 1 mod m, gcd(r, m) = 1 (r = 1 gives the direct product). For a
group G of order N and a d-element set S, the bipartite graph has L_g ~ R_{g s} for
s in S. It is d-regular, bipartite and simple. Left translations are automorphisms
transitive on each side, so diameter <= D reduces to two BFS runs (from L_e and R_e).

The C engine receives a list of group specs. It anneals a connection set for each
spec in ascending order of order N, with per-spec slices and an iterated search
around the incumbent set. The specs are passed through lib.run_c's graph channel
as pairs of integers. The parent's prime-power and generalized-quadrangle
constructions are kept as candidates, and K_{d,d} is the safe fallback.
"""
import itertools
import math
import random
import time

import numpy as np

import lib

C_SOURCE = r'''
/* Semidirect Haar lift search over groups Z_m x|_r Z_k.
 * Usage: prog d D seed time_limit      (stdin: header "n m", then m lines of pairs)
 * Spec i uses stdin lines 2i = "m k" and 2i+1 = "r 0". The first header is ignored.
 * Output: "n m" then m lines "u v" for the largest valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 16384
#define MAXD 32
#define MAXSPEC 8000

typedef struct { int m, k, r, N; } Spec;

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

/* Current group: element (a, b) is coded as a*K + b. (a,b)(c,e) = (a + r^b c, b + e). */
static int M, K, R, N;
static int pw[MAXN];

static void setup(Spec s) {
    M = s.m;
    K = s.k;
    N = s.m * s.k;
    R = s.r % M;
    pw[0] = 1 % M;
    for (int i = 1; i < K; i++) pw[i] = (pw[i - 1] * R) % M;
}

static inline int gmul(int x, int y) {
    int a = x / K, b = x % K, c = y / K, e = y % K;
    int na = (a + pw[b] * c) % M;
    int nb = (b + e) % K;
    return na * K + nb;
}

static int ginv(int x) {
    int a = x / K, b = x % K;
    int nb = (K - b) % K;
    int na = (M - (pw[nb] * a) % M) % M;
    return na * K + nb;
}

static int S[MAXD], bestS[MAXD], incS[MAXD];
static int fwd[MAXD][MAXN], bwd[MAXD][MAXN];
static int vis[2 * MAXN], que[2 * MAXN];
static int stamp_ = 0;

/* Vertices: L_g = g (0..N-1), R_h = N + h. L_g ~ R_{g s}, so R_h ~ L_{h s^-1}. */
static void set_s(int i, int x) {
    S[i] = x;
    int xi = ginv(x);
    for (int g = 0; g < N; g++) {
        fwd[i][g] = gmul(g, x);
        bwd[i][g] = gmul(g, xi);
    }
}

static int bfs_count(int src) {
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < N) {
                for (int i = 0; i < d; i++) {
                    int u = N + fwd[i][v];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int h = v - N;
                for (int i = 0; i < d; i++) {
                    int u = bwd[i][h];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

static long cover_cost(void) {
    int V = 2 * N;
    return (long)(V - bfs_count(0)) + (long)(V - bfs_count(N));
}

static int in_S(int x, int upto) {
    for (int i = 0; i < upto; i++)
        if (S[i] == x) return 1;
    return 0;
}

/* Iterated annealing: the first round starts random; later rounds perturb the
 * incumbent (two elements replaced) and anneal from a lower temperature.
 * Returns 1 when cost 0 is reached (S then holds a valid set), 0 on timeout. */
static int search(double until) {
    if (N <= d) return 0;
    const int iters = 6000;
    int have = 0;
    long bestc = 0;
    while (now() < until) {
        if (!have) {
            for (int i = 0; i < d; i++) {
                int x;
                do { x = rndint(N); } while (in_S(x, i));
                set_s(i, x);
            }
        } else {
            for (int i = 0; i < d; i++) set_s(i, incS[i]);
            for (int t = 0; t < 2; t++) {
                int i = rndint(d), x;
                do { x = rndint(N); } while (in_S(x, d));
                set_s(i, x);
            }
        }
        long cost = cover_cost();
        if (cost == 0) return 1;
        double c0 = (double)cost;
        double Ts = (have ? 0.02 : 0.05) * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int i = rndint(d), x;
            do { x = rndint(N); } while (in_S(x, d));
            int old = S[i];
            set_s(i, x);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                set_s(i, old);
            }
        }
        if (cost == 0) return 1;
        if (!have || cost < bestc) {
            have = 1;
            bestc = cost;
            memcpy(incS, S, sizeof(int) * (size_t)d);
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }

    int hn = 0, hm = 0;
    if (scanf("%d %d", &hn, &hm) != 2) hm = 0;
    static Spec sp[MAXSPEC];
    int ns = 0;
    for (int i = 0; i < hm / 2 && ns < MAXSPEC; i++) {
        int a, b, c, z;
        if (scanf("%d %d", &a, &b) != 2) break;
        if (scanf("%d %d", &c, &z) != 2) break;
        if (a < 2 || b < 1 || c < 0) continue;
        long NN = (long)a * b;
        if (NN > MAXN || NN <= d) continue;
        sp[ns].m = a;
        sp[ns].k = b;
        sp[ns].r = c;
        sp[ns].N = (int)NN;
        ns++;
    }

    /* Specs arrive in ascending order of N. Each attempt gets 12% of the remaining
     * time (at least 0.4 s), and only orders above the incumbent are tried. */
    int bestN = 0, bi = -1;
    for (int ci = 0; ci < ns; ci++) {
        double rem = t_end - now();
        if (rem < 0.3) break;
        if (sp[ci].N <= bestN) continue;
        double slice = 0.12 * rem;
        if (slice < 0.4) slice = 0.4;
        if (slice > rem) slice = rem;
        setup(sp[ci]);
        if (search(now() + slice)) {
            bestN = sp[ci].N;
            bi = ci;
            memcpy(bestS, S, sizeof(int) * (size_t)d);
        }
    }

    if (bi < 0) {
        printf("0 0\n");
        return 0;
    }
    setup(sp[bi]);
    for (int i = 0; i < d; i++) set_s(i, bestS[i]);
    printf("%d %d\n", 2 * N, N * d);
    for (int g = 0; g < N; g++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", g, N + fwd[i][g]);
    return 0;
}
'''


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
    """W(q) for the largest prime power q with q + 1 <= d (kept small for speed)."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _specs(lo, hi, seed, kmax=16, per_pair=3, per_n=6, cap=6000):
    """Semidirect specs (m, k, r) with lo <= m*k <= hi, k <= kmax, r^k = 1 mod m, gcd(r, m) = 1.

    Returned in ascending order of order N. Each (m, k) contributes at most per_pair
    random choices of r, and each N value at most per_n specs.
    """
    rng = random.Random(seed)
    out = []
    for k in range(1, kmax + 1):
        for m in range(max(2, -(-lo // k)), hi // k + 1):
            r = np.arange(m, dtype=np.int64)
            x = np.ones(m, dtype=np.int64)
            for _ in range(k):
                x = (x * r) % m
            ok = (x == 1) & (np.gcd(r, m) == 1)
            rs = [int(v) for v in r[ok]]
            if len(rs) > per_pair:
                rs = rng.sample(rs, per_pair)
            for rv in rs:
                out.append((m * k, m, k, rv))
    rng.shuffle(out)
    out.sort(key=lambda t: t[0])
    capped = []
    cnt = {}
    for t in out:
        c = cnt.get(t[0], 0)
        if c >= per_n:
            continue
        cnt[t[0]] = c + 1
        capped.append(t)
        if len(capped) >= cap:
            break
    return capped


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2, so it is valid for every D >= 2 and is the safe fallback.
    best = lib.haar_graph(d, range(d))

    def consider(cand):
        nonlocal best
        if cand is None:
            return
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        try:
            consider(_best_pg(d))
        except Exception:
            pass
        # Exact Moore graph: nothing can beat it.
        if D == 3 and lib.is_prime_power(d - 1) and best[0] > 2 * d:
            return best
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

    if D == 4:
        try:
            consider(_best_gq(d))
        except Exception:
            pass

    # Search over semidirect Haar lifts Z_m x|_r Z_k (includes the affine groups for prime q).
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
        lo = max(best[0] // 2 + 1, mb // 8, 2 * d + 1)
        hi = min(mb // 3, 16000)
        if budget > 2.0 and lo <= hi:
            try:
                specs = _specs(lo, hi, seed)
                if specs:
                    edges = []
                    for (_, m, k, r) in specs:
                        edges.append((m, k))
                        edges.append((r, 0))
                    text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                     stdin_graph=(len(specs), edges),
                                     timeout=budget + 8.0)
                    consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
